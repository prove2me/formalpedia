-- Prove2me | Theorems.Thm_ReusableMatching_lemma_6
-- name    : ReusableMatching.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:33:05.275011+00:00
-- url     : https://prove2.me/theorems/bb82840d-06c6-486c-b024-ba95309f29d9
-- title:
--   Lemma 6: lowering $y^1$ moves the match of $i$ in period $k(j)-1$ weakly earlier
-- statement:
--   Let an OBMRR instance and $\beta>0$ be given, fix an edge $(i,j)\in E$ and the seeds $Y_{-i,j}$, and fix $y^2\in[0,1]$. Let $z\in[0,1]$ be such that, for $y^1=z$, resource $i$ is matched to an arrival $t(z)$ of period $k(j)-1$. Then for every $y^1\le z$, resource $i$ is matched, in the run with seed $y^1$, to an arrival of period $k(j)-1$ that is $t(z)$ or precedes it.
--
--   This monotonicity in $y^1$ is what makes the three regimes of Lemma 7 intervals.
--
--   Differences from the source:
--   - reading: the lemma does not name y² → the statement holds for every y², the same in the run at y¹ = z and in the run at y¹ ≤ z; reason: the run up to the end of period k(j) − 1 does not read y² (proof, p.10)
--   - encoding: fixed seeds Y_{−i,j} and the run PR(y¹, y²) (p.9) → a full seed vector Y whose coordinates (i, k(j) − 1) and (i, k(j)) are overwritten by y¹, y² (twoSeed); the statement is for every Y; reason: Lean convention; every Y_{−i,j} is obtained this way, and the paper fixes an arbitrary Y_{−i,j}
--   - reading: arg max over the available neighbours, no tie rule (Algorithm 1, p.8) → the least maximizer for a linear order on V (a fixed priority order; V and its order are arbitrary); reason: the paper fixes no tie rule; its proofs of Lemmas 4, 6 and 8 compare runs at fixed seeds and need a choice among tied resources that does not depend on the seeds
--   - encoding: arrivals 1, …, |U|; periods of length d with a dummy period before the first arrival (p.8) → arrivals Fin n numbered from 0; arrival t lies in period t / d + 1; period 0 is the dummy period; seeds indexed by V × Fin (n + 1); reason: Lean convention; same instances and same runs
--   - encoding: d ∈ ℕ (p.2) → 1 ≤ d, as a field of the instance; reason: the model ("unavailable for the next d − 1 periods") has no meaning at d = 0
-- source:
--   Delong, Farhadi, Niazadeh, Sivan & Udwani, Online Bipartite Matching with Reusable Resources, arXiv:2110.07084v2, Lemma 6, p.10

import Mathlib
import Definitions.Def_ReusableMatching_PeriodicReranking
import Definitions.Def_ReusableMatching_twoSeed

namespace ReusableMatching

/-- **Lemma 6** of Delong, Farhadi, Niazadeh, Sivan & Udwani, arXiv:2110.07084v2, p.10, for a fixed
edge `(i, j) ∈ E` and fixed seeds `Y_{−i,j}`:

"Consider a value `z ∈ [0, 1]` such that for `y¹ = z`, `i` is matched to some arrival, say `t(z)`,
in period `k(j) − 1`. Then, for every `y¹ ≤ z`, `i` is matched in period `k(j) − 1` to arrival
`t(z)` or an arrival that precedes it."

**Formalization Note.**
* The lemma does not name `y²`; the run of period `k(j) − 1` does not read it ("The value of `y²`
  does not affect the output of PR in periods prior to `k(j)`", proof, p.10). The statement is for
  every `y²`, the same in the run at `y¹ = z` and in the run at `y¹ ≤ z`.
* "Arrival `t` in period `k(j) − 1`" is `period I t = prevPeriod I j`.
* `β > 0` (p.8; the proof uses the monotonicity of `g`). -/
theorem lemma_6 {V : Type*} [Fintype V] [LinearOrder V] {n : ℕ} (I : OBMRRInstance V n)
    (β : ℝ) (hβ : 0 < β) (i : V) (j : Fin n) (hij : (i, j) ∈ I.E) (Y : Seeds V n)
    (z y2 : unitInterval) (tz : Fin n) (htz : period I tz = prevPeriod I j)
    (hmatch : PeriodicReranking I β (twoSeed I Y i j z y2) tz = some i) :
    ∀ y1 : unitInterval, y1 ≤ z →
      ∃ t : Fin n, period I t = prevPeriod I j ∧ t ≤ tz ∧
        PeriodicReranking I β (twoSeed I Y i j y1 y2) t = some i := by sorry

end ReusableMatching
