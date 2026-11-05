-- Prove2me | Theorems.Thm_ReusableMatching_lemma_4
-- name    : ReusableMatching.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:34:33.010722+00:00
-- url     : https://prove2.me/theorems/38de756d-55f6-4a07-8dfa-8af396300dcf
-- title:
--   Lemma 4: bounds on $\beta_j$ and $\sum\alpha_{i,t}$ when $i\in S_{p(j)}(y^1,1)$
-- statement:
--   Let an OBMRR instance and $\beta>0$ be given, fix an edge $(i,j)\in E$ and the seeds $Y_{-i,j}$, and let $y^1\in[0,1]$ satisfy $i\in S_{p(j)}(y^1,1)$, that is, $i$ is available at some arrival of $p(j)$ in the run $\mathrm{PR}(y^1,1)$. Write $\beta_j(y^1,y^2)$ and $\alpha_{i,t}(y^1,y^2)$ for the dual variables of the run $\mathrm{PR}(y^1,y^2)$ and $y^c_j(y^1)$ for the critical threshold. Then for every $y^2\in[0,1]$:
--
--   1. $\beta_j(y^1,y^2)\ \ge\ \beta_j(y^1,1)\ \ge\ r_i\bigl(1-g(y^c_j(y^1))\bigr)$;
--   2. $$\sum_{t=\max\{j-d+1,1\}}^{j}\alpha_{i,t}(y^1,y^2)\ \ge\ \mathbf 1\bigl(y^2<y^c_j(y^1)\bigr)\, r_i\, g(y^2).$$
--
--   These are the reusable analogues of the per-edge bounds of the analysis of Perturbed Greedy; they cover the values of $y^1$ for which $i$ is available during $p(j)$.
--
--   Differences from the source:
--   - encoding: fixed seeds Y_{−i,j} and the run PR(y¹, y²) (p.9) → a full seed vector Y whose coordinates (i, k(j) − 1) and (i, k(j)) are overwritten by y¹, y² (twoSeed); the statement is for every Y; reason: Lean convention; every Y_{−i,j} is obtained this way, and the paper fixes an arbitrary Y_{−i,j}
--   - encoding: y^c_j(y¹): the solution of r_i(1 − g(y^c)) = max_{v ∈ S_j(y¹,1), (v,j) ∈ E} r_v(1 − g(y_v^{k(j)})), or 0 if there is none (p.9) → sup {y ∈ [0, 1] : M ≤ r_i(1 − g(y))}, which is 0 when the set is empty, with the max over no neighbour equal to 0; reason: for r_i > 0 and β > 0 this is the unique solution when one exists and 0 otherwise; for r_i = 0 every use of y^c carries the factor r_i or compares two thresholds of the same kind
--   - reading: arg max over the available neighbours, no tie rule (Algorithm 1, p.8) → the least maximizer for a linear order on V (a fixed priority order; V and its order are arbitrary); reason: the paper fixes no tie rule; its proofs of Lemmas 4, 6 and 8 compare runs at fixed seeds and need a choice among tied resources that does not depend on the seeds
--   - encoding: arrivals 1, …, |U|; periods of length d with a dummy period before the first arrival (p.8) → arrivals Fin n numbered from 0; arrival t lies in period t / d + 1; period 0 is the dummy period; seeds indexed by V × Fin (n + 1); reason: Lean convention; same instances and same runs
--   - encoding: d ∈ ℕ (p.2) → 1 ≤ d, as a field of the instance; reason: the model ("unavailable for the next d − 1 periods") has no meaning at d = 0
-- source:
--   Delong, Farhadi, Niazadeh, Sivan & Udwani, Online Bipartite Matching with Reusable Resources, arXiv:2110.07084v2, Lemma 4, p.9 (proof in Appendix C, pp.33–34)

import Mathlib
import Definitions.Def_ReusableMatching_dualBeta
import Definitions.Def_ReusableMatching_dualAlpha
import Definitions.Def_ReusableMatching_availableInSubperiod
import Definitions.Def_ReusableMatching_criticalThreshold
import Definitions.Def_ReusableMatching_window

namespace ReusableMatching

/-- **Lemma 4** of Delong, Farhadi, Niazadeh, Sivan & Udwani, arXiv:2110.07084v2, p.9 (proof in
Appendix C, pp.33–34), for a fixed edge `(i, j) ∈ E` and fixed seeds `Y_{−i,j}`:

"Given `y¹ ∈ [0, 1]` such that `i ∈ S_{p(j)}(y¹, 1)`, we have,
a) `β_j(y¹, y²) ≥ β_j(y¹, 1) ≥ r_i (1 − g(y^c_j(y¹)))` `∀ y² ∈ [0, 1]`.
b) `∑_{t = max{j−d+1,1}}^{j} α_{i,t}(y¹, y²) ≥ 1(y² < y^c_j(y¹)) r_i g(y²)` `∀ y² ∈ [0, 1]`."

**Formalization Note.**
* `Y_{−i,j}` is a full seed vector `Y` whose coordinates `(i, k(j) − 1)`, `(i, k(j))` are
  overwritten by `y¹`, `y²` (`twoSeed`); the statement holds for every `Y`, as the paper fixes an
  arbitrary `Y_{−i,j}` (p.9).
* `β_j(y¹, y²)` is `dualBeta` at `twoSeed I Y i j y¹ y²`, `α_{i,t}(y¹, y²)` is `dualAlpha` there,
  `S_{p(j)}(y¹, 1)` is `availableInSubperiod` at `twoSeed I Y i j y¹ 1`, and `y^c_j(y¹)` is
  `criticalThreshold I β Y i j y¹ j`.
* The indicator `1(y² < y^c_j(y¹))` is an `if`.
* `β > 0` (p.8; the proof uses that `g` is strictly increasing). -/
theorem lemma_4 {V : Type*} [Fintype V] [LinearOrder V] {n : ℕ} (I : OBMRRInstance V n)
    (β : ℝ) (hβ : 0 < β) (i : V) (j : Fin n) (hij : (i, j) ∈ I.E) (Y : Seeds V n)
    (y1 : unitInterval) (hi : i ∈ availableInSubperiod I β (twoSeed I Y i j y1 1) j) :
    (∀ y2 : unitInterval,
      dualBeta I β (twoSeed I Y i j y1 1) j ≤ dualBeta I β (twoSeed I Y i j y1 y2) j) ∧
    I.r i * (1 - g β (criticalThreshold I β Y i j y1 j)) ≤
      dualBeta I β (twoSeed I Y i j y1 1) j ∧
    (∀ y2 : unitInterval,
      (if (y2 : ℝ) < criticalThreshold I β Y i j y1 j then I.r i * g β y2 else 0) ≤
        ∑ t ∈ window I j, dualAlpha I β (twoSeed I Y i j y1 y2) i t) := by sorry

end ReusableMatching
