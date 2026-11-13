-- Prove2me | Theorems.Thm_StableCount_theorem_3
-- name    : StableCount.theorem_3
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T10:51:23.418278+00:00
-- url     : https://prove2.me/theorems/97cba089-2b51-4393-a415-a8481dbbce0a
-- title:
--   Theorem 3 — an admissible sequence with sum below $\ln 2.81$
-- statement:
--   There exists an admissible sequence $(h_r)_{r\ge 1}$ such that
--   $$
--   \sum_{r=1}^\infty h_r<\ln 2.81.
--   $$
--   The paper's sequence has the 32 values of its Table 2, and $h_d=C/(d(d-1))$ for $d\ge 33$ with $C=2.013448663125$. Its sum is $S=1.03307089361665625$, with $e^S\approx 2.809680831$.
--
--   Differences from the source:
--   - encoding: a sequence h₁, h₂, … → h : ℕ → ℝ, with h 0 never read; reason: Lean convention; same sequences
--   - encoding: ∑_{d≥1} h_d is finite, or is below ln 2.81 with positive terms → Summable (d ↦ h (d+1)) together with the value of ∑' d, h (d+1); reason: tsum is 0 for a non-summable family, so the sum clause alone would say nothing; a series of positive terms below a bound converges
--   - encoding: λ(t) for t > 0 → lam on all of ℝ, with lam 0 = 0 from Real.log 0 = 0; reason: never hit: for an admissible sequence every argument is positive (p.15)
-- source:
--   Ghorbani, Mnich, A 2.81^n upper bound on the number of stable matchings, arXiv:2611.06494 (held PDF sha256 9445f6a8…), Theorem 3, p.5 (PDF p.6); proof pp.33–34

import Mathlib
import Definitions.Def_StableCount_Potential

namespace StableCount

/-- Theorem 3 (arXiv:2611.06494, held PDF sha256 9445f6a8…, Theorem 3, p.5; proof pp.33–34). There exists an admissible sequence `(h_r)_{r≥1}`
such that `∑_{r=1}^∞ h_r < ln 2.81`.

**Formalization Note** `Summable` is stated, since `tsum` is `0` otherwise. The indices start at
`d + 1 ≥ 1`: `h 0` is not read. -/
theorem theorem_3 :
    ∃ h : ℕ → ℝ, IsAdmissible h ∧ Summable (fun d => h (d + 1)) ∧
      ∑' d, h (d + 1) < Real.log 2.81 := by sorry

end StableCount
