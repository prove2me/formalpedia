-- Prove2me | Theorems.Thm_ReusableMatching_lemma_3
-- name    : ReusableMatching.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:33:50.766359+00:00
-- url     : https://prove2.me/theorems/5b1c9d40-1b6a-4494-a1b6-8441d09109a8
-- title:
--   Lemma 3: the conditional bound (3) for every $Y_{-i,j}$ gives approximate dual feasibility
-- statement:
--   Let an OBMRR instance and $\beta>0$ be given, let $(i,j)\in E$ and $\Gamma>0$. Suppose that for every choice of the seeds $Y_{-i,j}$ (all seeds except $y^1=y_i^{k(j)-1}$ and $y^2=y_i^{k(j)}$)
--
--   $$
--   \mathbb E_{y^1,y^2}\Bigl[\beta_j(Y)+\sum_{t=\max\{j-d+1,1\}}^{j}\alpha_{i,t}(Y)\ \Big|\ Y_{-i,j}\Bigr]\ \ge\ \Gamma\, r_i, \tag{3}
--   $$
--
--   where $y^1,y^2$ are independent and uniform on $[0,1]$. Then the edge $(i,j)$ satisfies constraint (ii) of Lemma 1 with the same $\Gamma$:
--
--   $$
--   \mathbb E_Y[\beta_j(Y)]+\sum_{t=\max\{j-d+1,1\}}^{j}\mathbb E_Y[\alpha_{i,t}(Y)]\ \ge\ \Gamma\, r_i .
--   $$
--
--   This reduces approximate dual feasibility to a bound in which only the two seeds of $i$ around the period of $j$ are random.
--
--   Differences from the source:
--   - reading: (3) is conditioned on Y_{−i,t} → conditioned on Y_{−i,j}; reason: the lemma fixes the seed Y_{−i,j} and its proof takes the expectation over Y_{−i,j}
--   - reading: "Consider an edge (i,j) ∈ E and seed Y_{−i,j}. Suppose … (3)" → (3) is assumed for every seed vector Y; reason: the conclusion is unconditional and its proof averages (3) over Y_{−i,j}; the paper proves (3) "for every edge (i,j) ∈ E and seed Y_{−i,j}" (p.9)
--   - encoding: conditional expectation E_{y¹,y²}[· | Y_{−i,j}] → the double integral over y¹, y² ∈ unitInterval of the quantity at twoSeed I Y i j y¹ y²; reason: y¹, y² are independent uniform seeds independent of Y_{−i,j}
--   - encoding: E_Y[·] over i.i.d. U[0,1] seeds → Bochner integral with respect to seedMeasure, the product of the uniform measures on unitInterval; reason: Lean convention; the integrands are bounded
--   - reading: arg max over the available neighbours, no tie rule (Algorithm 1, p.8) → the least maximizer for a linear order on V (a fixed priority order; V and its order are arbitrary); reason: the paper fixes no tie rule; its proofs of Lemmas 4, 6 and 8 compare runs at fixed seeds and need a choice among tied resources that does not depend on the seeds
--   - encoding: arrivals 1, …, |U|; periods of length d with a dummy period before the first arrival (p.8) → arrivals Fin n numbered from 0; arrival t lies in period t / d + 1; period 0 is the dummy period; seeds indexed by V × Fin (n + 1); reason: Lean convention; same instances and same runs
--   - encoding: d ∈ ℕ (p.2) → 1 ≤ d, as a field of the instance; reason: the model ("unavailable for the next d − 1 periods") has no meaning at d = 0
-- source:
--   Delong, Farhadi, Niazadeh, Sivan & Udwani, Online Bipartite Matching with Reusable Resources, arXiv:2110.07084v2, Lemma 3, p.9

import Mathlib
import Definitions.Def_ReusableMatching_dualBeta
import Definitions.Def_ReusableMatching_dualAlpha
import Definitions.Def_ReusableMatching_twoSeed
import Definitions.Def_ReusableMatching_window

namespace ReusableMatching

open MeasureTheory

/-- **Lemma 3 (conditioning on `Y_{−i,j}`)** of Delong, Farhadi, Niazadeh, Sivan & Udwani,
arXiv:2110.07084v2, p.9:

"Consider an edge `(i, j) ∈ E` and seed `Y_{−i,j}`. Suppose that for the candidate solution given
by (1) and (2), we have
`E_{y_i^{k(j)}, y_i^{k(j)−1}} [ β_j(Y) + ∑_{t = max{j−d+1,1}}^{j} α_{i,t}(Y) | Y_{−i,t} ] ≥ Γ r_i`, (3)
for some value `Γ > 0`. Then, constraint (ii) of Lemma 1 is satisfied for edge `(i, j) ∈ E` with
the same `Γ`."

Constraint (ii) for the edge `(i, j)` is `β_j + ∑_{t} α_{i,t} ≥ Γ r_i` with `β_j = E_Y[β_j(Y)]`,
`α_{i,t} = E_Y[α_{i,t}(Y)]`.

**Formalization Note.**
* The conditional expectation in (3) given `Y_{−i,j}` is the double integral over the two seeds
  `y¹ = y_i^{k(j)−1}`, `y² = y_i^{k(j)}`, uniform on `[0, 1]`, of the quantity at the seed vector
  `twoSeed I Y i j y¹ y²`. The paper proves (3) "for every edge `(i, j) ∈ E` and seed `Y_{−i,j}`"
  (p.9); accordingly the hypothesis quantifies over every seed vector `Y`.
* The subscript `Y_{−i,t}` in (3) is read as `Y_{−i,j}`, the seed fixed in the lemma.
* `β > 0` is the paper's standing range (p.8). -/
theorem lemma_3 {V : Type*} [Fintype V] [LinearOrder V] {n : ℕ} (I : OBMRRInstance V n)
    (β : ℝ) (hβ : 0 < β) (i : V) (j : Fin n) (hij : (i, j) ∈ I.E) (Γ : ℝ) (hΓ : 0 < Γ)
    (h3 : ∀ Y : Seeds V n, Γ * I.r i ≤
      ∫ y1 : unitInterval, ∫ y2 : unitInterval,
        (dualBeta I β (twoSeed I Y i j y1 y2) j +
          ∑ t ∈ window I j, dualAlpha I β (twoSeed I Y i j y1 y2) i t)) :
    Γ * I.r i ≤
      ∫ Y, dualBeta I β Y j ∂(seedMeasure V n) +
        ∑ t ∈ window I j, ∫ Y, dualAlpha I β Y i t ∂(seedMeasure V n) := by sorry

end ReusableMatching
