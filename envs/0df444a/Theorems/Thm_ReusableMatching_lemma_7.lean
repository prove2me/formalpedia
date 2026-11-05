-- Prove2me | Theorems.Thm_ReusableMatching_lemma_7
-- name    : ReusableMatching.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:35:22.626198+00:00
-- url     : https://prove2.me/theorems/39277ba5-b30c-4094-bd06-2ac6a5551188
-- title:
--   Lemma 7: thresholds $z_1\le z_2$ split $y^1$ into three regimes
-- statement:
--   Let an OBMRR instance and $\beta>0$ be given, and fix an edge $(i,j)\in E$ and the seeds $Y_{-i,j}$. There exist $z_1,z_2\in[0,1]$ with $z_1\le z_2$ such that, in the run $\mathrm{PR}(y^1,1)$:
--
--   1. for every $y^1\in(z_2,1]$, $i\in S_{p(j)}(y^1,1)$ and $i$ is not matched to any arrival in period $k(j)-1$;
--   2. for every $y^1\in(z_1,z_2)$, $i\notin S_{p(j)}(y^1,1)$ and $i$ is matched to some arrival in period $k(j)-1$;
--   3. for every $y^1\in[0,z_1)$, $i\in S_{p(j)}(y^1,1)$ and $i$ is matched to some arrival in period $k(j)-1$.
--
--   In the analysis, regime 1 and regime 3 are handled by Lemma 4 and regime 2 by Lemma 5.
--
--   Differences from the source:
--   - encoding: fixed seeds Y_{−i,j} and the run PR(y¹, y²) (p.9) → a full seed vector Y whose coordinates (i, k(j) − 1) and (i, k(j)) are overwritten by y¹, y² (twoSeed); the statement is for every Y; reason: Lean convention; every Y_{−i,j} is obtained this way, and the paper fixes an arbitrary Y_{−i,j}
--   - reading: arg max over the available neighbours, no tie rule (Algorithm 1, p.8) → the least maximizer for a linear order on V (a fixed priority order; V and its order are arbitrary); reason: the paper fixes no tie rule; its proofs of Lemmas 4, 6 and 8 compare runs at fixed seeds and need a choice among tied resources that does not depend on the seeds
--   - encoding: arrivals 1, …, |U|; periods of length d with a dummy period before the first arrival (p.8) → arrivals Fin n numbered from 0; arrival t lies in period t / d + 1; period 0 is the dummy period; seeds indexed by V × Fin (n + 1); reason: Lean convention; same instances and same runs
--   - encoding: d ∈ ℕ (p.2) → 1 ≤ d, as a field of the instance; reason: the model ("unavailable for the next d − 1 periods") has no meaning at d = 0
-- source:
--   Delong, Farhadi, Niazadeh, Sivan & Udwani, Online Bipartite Matching with Reusable Resources, arXiv:2110.07084v2, Lemma 7, pp.10–11

import Mathlib
import Definitions.Def_ReusableMatching_ThreeRegimes

namespace ReusableMatching

/-- **Lemma 7** of Delong, Farhadi, Niazadeh, Sivan & Udwani, arXiv:2110.07084v2, pp.10–11, for a
fixed edge `(i, j) ∈ E` and fixed seeds `Y_{−i,j}`:

"There exists values `z1, z2 ∈ [0, 1]`, such that `z1 ≤ z2` and,
a) `i ∈ S_{p(j)}(y¹, 1)` `∀ y¹ ∈ (z2, 1]` and `i` is not matched to any arrival in period `k(j) − 1`.
b) `i ∉ S_{p(j)}(y¹, 1)` `∀ y¹ ∈ (z1, z2)` and `i` is matched to some arrival in period `k(j) − 1`.
c) `i ∈ S_{p(j)}(y¹, 1)` `∀ y¹ ∈ [0, z1)` and `i` is matched to some arrival in period `k(j) − 1`."

**Formalization Note.** The three properties are `ThreeRegimes I β Y i j z1 z2`; "matched in period
`k(j) − 1`" refers to the run `PR(y¹, 1)` (that period does not read `y²`). The statement holds for
every seed vector `Y` (every `Y_{−i,j}`), and `β > 0` (p.8). -/
theorem lemma_7 {V : Type*} [Fintype V] [LinearOrder V] {n : ℕ} (I : OBMRRInstance V n)
    (β : ℝ) (hβ : 0 < β) (i : V) (j : Fin n) (hij : (i, j) ∈ I.E) (Y : Seeds V n) :
    ∃ z1 z2 : unitInterval, z1 ≤ z2 ∧ ThreeRegimes I β Y i j z1 z2 := by sorry

end ReusableMatching
