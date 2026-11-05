-- Prove2me | Theorems.Thm_ReusableMatching_lemma_5
-- name    : ReusableMatching.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:34:49.169325+00:00
-- url     : https://prove2.me/theorems/d2d80482-fc31-4b79-bb03-263744f78994
-- title:
--   Lemma 5: the bound on $\sum\alpha_{i,t}$ when $i\notin S_{p(j)}(y^1,1)$
-- statement:
--   Let an OBMRR instance and $\beta>0$ be given, fix an edge $(i,j)\in E$ and the seeds $Y_{-i,j}$, and let $y^1\in[0,1]$ satisfy $i\notin S_{p(j)}(y^1,1)$, that is, $i$ is unavailable at every arrival of $p(j)$ in the run $\mathrm{PR}(y^1,1)$. Then for every $y^2\in[0,1]$
--
--   $$
--   \sum_{t=\max\{j-d+1,1\}}^{j}\alpha_{i,t}(y^1,y^2)\ \ge\ r_i\, g(y^1).
--   $$
--
--   Lemmas 4 and 5 cover complementary cases; together they bound $\sum_t\alpha_{i,t}(y^1,y^2)$ for all $(y^1,y^2)\in[0,1]^2$.
--
--   Differences from the source:
--   - encoding: fixed seeds Y_{−i,j} and the run PR(y¹, y²) (p.9) → a full seed vector Y whose coordinates (i, k(j) − 1) and (i, k(j)) are overwritten by y¹, y² (twoSeed); the statement is for every Y; reason: Lean convention; every Y_{−i,j} is obtained this way, and the paper fixes an arbitrary Y_{−i,j}
--   - reading: arg max over the available neighbours, no tie rule (Algorithm 1, p.8) → the least maximizer for a linear order on V (a fixed priority order; V and its order are arbitrary); reason: the paper fixes no tie rule; its proofs of Lemmas 4, 6 and 8 compare runs at fixed seeds and need a choice among tied resources that does not depend on the seeds
--   - encoding: arrivals 1, …, |U|; periods of length d with a dummy period before the first arrival (p.8) → arrivals Fin n numbered from 0; arrival t lies in period t / d + 1; period 0 is the dummy period; seeds indexed by V × Fin (n + 1); reason: Lean convention; same instances and same runs
--   - encoding: d ∈ ℕ (p.2) → 1 ≤ d, as a field of the instance; reason: the model ("unavailable for the next d − 1 periods") has no meaning at d = 0
-- source:
--   Delong, Farhadi, Niazadeh, Sivan & Udwani, Online Bipartite Matching with Reusable Resources, arXiv:2110.07084v2, Lemma 5, p.10

import Mathlib
import Definitions.Def_ReusableMatching_dualAlpha
import Definitions.Def_ReusableMatching_availableInSubperiod
import Definitions.Def_ReusableMatching_twoSeed
import Definitions.Def_ReusableMatching_window

namespace ReusableMatching

/-- **Lemma 5** of Delong, Farhadi, Niazadeh, Sivan & Udwani, arXiv:2110.07084v2, p.10, for a fixed
edge `(i, j) ∈ E` and fixed seeds `Y_{−i,j}`:

"Given `y¹ ∈ [0, 1]` such that `i ∉ S_{p(j)}(y¹, 1)`, we have,
`∑_{t = max{j−d+1,1}}^{j} α_{i,t}(y¹, y²) ≥ r_i g(y¹)` `∀ y² ∈ [0, 1]`."

**Formalization Note.** Same conventions as Lemma 4: the run `PR(y¹, y²)` is the run at
`twoSeed I Y i j y¹ y²`, the statement holds for every seed vector `Y`, and `β > 0` (p.8). -/
theorem lemma_5 {V : Type*} [Fintype V] [LinearOrder V] {n : ℕ} (I : OBMRRInstance V n)
    (β : ℝ) (hβ : 0 < β) (i : V) (j : Fin n) (hij : (i, j) ∈ I.E) (Y : Seeds V n)
    (y1 : unitInterval) (hi : i ∉ availableInSubperiod I β (twoSeed I Y i j y1 1) j) :
    ∀ y2 : unitInterval,
      I.r i * g β y1 ≤ ∑ t ∈ window I j, dualAlpha I β (twoSeed I Y i j y1 y2) i t := by sorry

end ReusableMatching
