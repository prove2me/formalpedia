-- Prove2me | Theorems.Thm_QuarterSumLadder_vlam_B2
-- name    : QuarterSumLadder.vlam_B2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:12:51.232961+00:00
-- url     : https://prove2.me/theorems/423c8435-7117-5c61-add8-739499519fd2
-- title:
--   Quarter Sum Ladder: vlam B2
-- statement:
--   **The weight-two trichotomy** (Paper IV, Theorem 8.2) in valuation form: `v_λ(B_{2,χ}) = 5` if
--   `χ(2) = -1`, `= 6` if `χ(2) = 1` and `p ≡ 9 (mod 16)`, and `≥ 7` if `χ(2) = 1`, `p ≡ 1 (mod 16)` and
--   `B_{2,χ} ≠ 0` (which holds since `L(-1, χ) ≠ 0`, not formalized).
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Boundary.lean#L248-L255
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Boundary.lean#L248-L255

module
public import Definitions.Def_QuarterSumLadder_Ladder
public import Definitions.Def_QuarterSumLadder_Boundary
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
variable {p : ℕ} [hp : Fact p.Prime] {χ : MulChar (ZMod p) GaussianInt}
  (hp8 : p % 8 = 1) (hχ : orderOf χ = 4)
include hp8 hχ

theorem QuarterSumLadder.vlam_B2 :
    (χ 2 = -1 → vlam (B2 χ) = 5) ∧ (χ 2 = 1 → p % 16 = 9 → vlam (B2 χ) = 6) ∧
      (χ 2 = 1 → p % 16 = 1 → B2 χ ≠ 0 → 7 ≤ vlam (B2 χ)) := by sorry
