-- Prove2me | Theorems.Thm_QuarterSumLadder_vlam_Omega
-- name    : QuarterSumLadder.vlam_Omega
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:12:54.326971+00:00
-- url     : https://prove2.me/theorems/206e59b9-dc2f-5dfa-bf8b-0eb633698243
-- title:
--   Quarter Sum Ladder: vlam Omega
-- statement:
--   **The first three thresholds** (Paper IV, Theorem 5.2) in valuation form: `v_λ(Ω) = 1` if
--   `χ(2) = -1`, `v_λ(Ω) = 2` if `χ(2) = 1` and `p ≡ 9 (mod 16)`, and `v_λ(Ω) ≥ 3` if `χ(2) = 1`,
--   `p ≡ 1 (mod 16)` and `Ω ≠ 0` (which holds since `h⁻(K) = 2N(Ω) ≠ 0`, not formalized).
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Boundary.lean#L236-L243
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Boundary.lean#L236-L243

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

theorem QuarterSumLadder.vlam_Omega :
    (χ 2 = -1 → vlam (Omega χ) = 1) ∧ (χ 2 = 1 → p % 16 = 9 → vlam (Omega χ) = 2) ∧
      (χ 2 = 1 → p % 16 = 1 → Omega χ ≠ 0 → 3 ≤ vlam (Omega χ)) := by sorry
