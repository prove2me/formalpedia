-- Prove2me | Theorems.Thm_ReusableMatching_lemma_9
-- name    : ReusableMatching.lemma_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:34:50.825395+00:00
-- url     : https://prove2.me/theorems/902216ff-1d3b-4a60-888e-dfbacdf9339a
-- title:
--   Lemma 9: the combined lower bound on $\mathbb E_{y^1,y^2}[\beta_j+\sum\alpha_{i,t}]$
-- statement:
--   Let an OBMRR instance and $\beta\in(0,1]$ be given, let $g(x)=e^{\beta(x-1)}$ and let $G$ be an antiderivative of $g$. Fix an edge $(i,j)\in E$ and the seeds $Y_{-i,j}$, and write $x=y^c_j(1)$. There exist $z_1,z_2\in[0,1]$ with $z_1\le z_2$ such that
--
--   $$
--   \mathbb E_{y^1,y^2}\Bigl[\beta_j(y^1,y^2)+\sum_{t=\max\{j-d+1,1\}}^{j}\alpha_{i,t}(y^1,y^2)\Bigr]
--   \ \ge\ r_i\Bigl[G(z_2)-G(z_1)+(1-g(x))(1-z_1)+(1-z_2)\bigl(G(x)-G(0)\bigr)+z_1\bigl(1-g(0)\bigr)\Bigr],
--   $$
--
--   where $y^1,y^2$ are independent and uniform on $[0,1]$. The bracket is $f(z_1,z_2,x)$; with the minimization of the proof of Theorem 1 this gives (3) with $\Gamma=0.5893$.
--
--   Differences from the source:
--   - reading: y^c_t(1) in the bound → y^c_j(1), the critical threshold at the arrival j of the edge; reason: the proof of Lemma 9 (p.12) uses y^c_j(1) throughout
--   - encoding: G is an antiderivative of g → G(x) = g(x)/β; reason: only differences of G occur
--   - encoding: fixed seeds Y_{−i,j} and the run PR(y¹, y²) (p.9) → a full seed vector Y whose coordinates (i, k(j) − 1) and (i, k(j)) are overwritten by y¹, y² (twoSeed); the statement is for every Y; reason: Lean convention; every Y_{−i,j} is obtained this way, and the paper fixes an arbitrary Y_{−i,j}
--   - encoding: conditional expectation E_{y¹,y²}[· | Y_{−i,j}] → the double integral over y¹, y² ∈ unitInterval of the quantity at twoSeed I Y i j y¹ y²; reason: y¹, y² are independent uniform seeds independent of Y_{−i,j}
--   - encoding: y^c_j(y¹): the solution of r_i(1 − g(y^c)) = max_{v ∈ S_j(y¹,1), (v,j) ∈ E} r_v(1 − g(y_v^{k(j)})), or 0 if there is none (p.9) → sup {y ∈ [0, 1] : M ≤ r_i(1 − g(y))}, which is 0 when the set is empty, with the max over no neighbour equal to 0; reason: for r_i > 0 and β > 0 this is the unique solution when one exists and 0 otherwise; for r_i = 0 every use of y^c carries the factor r_i or compares two thresholds of the same kind
--   - reading: arg max over the available neighbours, no tie rule (Algorithm 1, p.8) → the least maximizer for a linear order on V (a fixed priority order; V and its order are arbitrary); reason: the paper fixes no tie rule; its proofs of Lemmas 4, 6 and 8 compare runs at fixed seeds and need a choice among tied resources that does not depend on the seeds
--   - encoding: arrivals 1, …, |U|; periods of length d with a dummy period before the first arrival (p.8) → arrivals Fin n numbered from 0; arrival t lies in period t / d + 1; period 0 is the dummy period; seeds indexed by V × Fin (n + 1); reason: Lean convention; same instances and same runs
--   - encoding: d ∈ ℕ (p.2) → 1 ≤ d, as a field of the instance; reason: the model ("unavailable for the next d − 1 periods") has no meaning at d = 0
-- source:
--   Delong, Farhadi, Niazadeh, Sivan & Udwani, Online Bipartite Matching with Reusable Resources, arXiv:2110.07084v2, Lemma 9, p.11 (proof pp.12–13)

import Mathlib
import Definitions.Def_ReusableMatching_dualBeta
import Definitions.Def_ReusableMatching_dualAlpha
import Definitions.Def_ReusableMatching_criticalThreshold
import Definitions.Def_ReusableMatching_window
import Definitions.Def_ReusableMatching_G__bf4f7e

namespace ReusableMatching

/-- **Lemma 9** of Delong, Farhadi, Niazadeh, Sivan & Udwani, arXiv:2110.07084v2, p.11 (proof
pp.12–13), for a fixed edge `(i, j) ∈ E` and fixed seeds `Y_{−i,j}`, with `g(x) = e^{β(x−1)}` for
some `β ∈ (0, 1]` and `G` an antiderivative of `g` (p.11):

"There exists values `z1, z2 ∈ [0, 1]` with `z1 ≤ z2`, such that
`E_{y¹,y²} [ β_j(y¹, y²) + ∑_{t = max{j−d+1,1}}^{j} α_{i,t}(y¹, y²) ]
  ≥ r_i [ G(z2) − G(z1) + (1 − g(y^c_t(1)))(1 − z1) + (1 − z2)(G(y^c_t(1)) − G(0)) + z1(1 − g(0)) ]`."

**Formalization Note.**
* `E_{y¹,y²}[·]` is the conditional expectation given `Y_{−i,j}`: the double integral over
  `y¹, y² ∈ [0, 1]` (uniform) at the seed vector `twoSeed I Y i j y¹ y²`. The statement holds for
  every seed vector `Y` (every `Y_{−i,j}`).
* `y^c_t(1)` is read as `y^c_j(1)`, the critical threshold at the arrival `j` of the edge, as in the
  proof (p.12): `criticalThreshold I β Y i j 1 j`.
* `G(x) = g(x)/β` (`G`); only differences of `G` occur. -/
theorem lemma_9 {V : Type*} [Fintype V] [LinearOrder V] {n : ℕ} (I : OBMRRInstance V n)
    (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) (i : V) (j : Fin n) (hij : (i, j) ∈ I.E)
    (Y : Seeds V n) :
    ∃ z1 z2 : ℝ, 0 ≤ z1 ∧ z1 ≤ z2 ∧ z2 ≤ 1 ∧
      I.r i * (G β z2 - G β z1 + (1 - g β (criticalThreshold I β Y i j 1 j)) * (1 - z1) +
          (1 - z2) * (G β (criticalThreshold I β Y i j 1 j) - G β 0) + z1 * (1 - g β 0)) ≤
        ∫ y1 : unitInterval, ∫ y2 : unitInterval,
          (dualBeta I β (twoSeed I Y i j y1 y2) j +
            ∑ t ∈ window I j, dualAlpha I β (twoSeed I Y i j y1 y2) i t) := by sorry

end ReusableMatching
