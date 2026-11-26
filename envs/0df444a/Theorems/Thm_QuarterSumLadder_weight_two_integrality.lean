-- Prove2me | Theorems.Thm_QuarterSumLadder_weight_two_integrality
-- name    : QuarterSumLadder.weight_two_integrality
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:16:54.366389+00:00
-- url     : https://prove2.me/theorems/06adde9d-d0ea-5a66-bec3-26f26bad0a58
-- title:
--   Quarter Sum Ladder: weight two integrality
-- statement:
--   **The coordinates of `B_{2,χ}` are integers** (proof of Theorem 3.1): `p ∣ U_z`, `p c₀ = U₁ - U₋₁`,
--   `p c₁ = U_i - U_{-i}`, and `∑_{0<m<p} χ(m) m² = p B_{2,χ}`.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/Solution.lean#L38-L41
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/Solution.lean#L38-L41

module
public import Definitions.Def_QuarterSumLadder
public import Definitions.Def_QuarterSumLadder_Solution
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuarterSumLadder.weight_two_integrality {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4) :
    (∀ z : GaussianInt, (p : ℤ) ∣ U χ z) ∧ (p : ℤ) * c0 χ = U χ 1 - U χ (-1) ∧
      (p : ℤ) * c1 χ = U χ gi - U χ (-gi) ∧ T2 χ = (p : GaussianInt) * B2 χ := by sorry
