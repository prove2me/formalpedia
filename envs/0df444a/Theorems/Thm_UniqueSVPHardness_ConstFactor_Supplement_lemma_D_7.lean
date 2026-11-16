-- Prove2me | Theorems.Thm_UniqueSVPHardness_ConstFactor_Supplement_lemma_D_7
-- name    : UniqueSVPHardness.ConstFactor.Supplement.lemma_D_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T12:53:49.869988+00:00
-- url     : https://prove2.me/theorems/479f347c-a87b-4c4f-a2c8-d1025dafade8
-- title:
--   Lemma D.7 — short simultaneous cancellation
-- statement:
--   Let $P$ be prime, $T\ge0$, and $b=\lceil (T+1)\log_2P\rceil$. If $P\ge2(b+1)$, there is a nonzero vector $c\in\{-1,0,1\}^{\mathbb F_P}$ with
--   $$\sum_w c_w=0\ \text{over }\mathbb Z,\qquad \sum_w c_w w^j=0\ \text{over }\mathbb F_P\ (0\le j\le T),\qquad \|c\|_2^2\le2(b+1),$$
--   where $w^0=1$ also for $w=0$.
--
--   Placed in a single fiber, this vector gives the short lattice vector of Theorem D.8.
--
--   Differences from the source:
--
--   - encoding: ‖c‖₂² → ∑_w c_w² in ℤ; reason: same quantity
--   - encoding: b = ⌈(T + 1) log₂ P⌉ → the natural-number ceiling of the real (T + 1) log₂ P; reason: same value
-- source:
--   Sergei Kudria, Jason Luo, STOC 2027 submission #1647 (October 2026), p. 45, Lemma D.7

import Mathlib

set_option autoImplicit false

namespace UniqueSVPHardness.ConstFactor.Supplement

/-- Lemma D.7 (short simultaneous cancellation). Let `P` be prime, `T ≥ 0`, and
`b = ⌈(T + 1) log₂ P⌉`. If `P ≥ 2(b + 1)`, there is a nonzero `c ∈ {−1, 0, 1}^{F_P}` with
`∑_w c_w = 0` over `ℤ`, `∑_w c_w w^j = 0` over `F_P` for `0 ≤ j ≤ T` (with `w^0 = 1`), and
`‖c‖₂² ≤ 2(b + 1)`. -/
theorem lemma_D_7 (P : ℕ) [Fact P.Prime] (T : ℕ)
    (hP : 2 * (⌈((T : ℝ) + 1) * Real.logb 2 P⌉₊ + 1) ≤ P) :
    ∃ c : ZMod P → ℤ, c ≠ 0 ∧ (∀ w, c w = -1 ∨ c w = 0 ∨ c w = 1) ∧
      ∑ w, c w = 0 ∧
      (∀ j ≤ T, ∑ w : ZMod P, (c w : ZMod P) * w ^ j = 0) ∧
      ∑ w, c w ^ 2 ≤ 2 * ((⌈((T : ℝ) + 1) * Real.logb 2 P⌉₊ : ℤ) + 1) := by sorry

end UniqueSVPHardness.ConstFactor.Supplement
