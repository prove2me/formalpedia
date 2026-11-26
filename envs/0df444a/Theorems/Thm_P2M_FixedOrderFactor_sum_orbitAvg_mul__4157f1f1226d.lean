-- Prove2me | Theorems.Thm_P2M_FixedOrderFactor_sum_orbitAvg_mul__4157f1f1226d
-- name    : P2M_FixedOrderFactor_sum_orbitAvg_mul__4157f1f1226d
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:48:04.210867+00:00
-- url     : https://prove2.me/theorems/ad4216b8-8b00-52bf-aafc-9bf4b5de4217
-- title:
--   P2 M Fixed Order Factor sum orbit Avg mul  4157f1f1226d: P2 M Fixed Order Factor sum orbit Avg mul  4157f1f1226d
-- statement:
--   `∑_{t<s} ϱ_s(ct) = s` if `s ∣ c` and `0` otherwise.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Bias.lean#L59-L78
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Bias.lean#L59-L78

module
public import Definitions.Def_FixedOrderFactor_Local
public import Definitions.Def_FixedOrderFactor_Bias
set_option autoImplicit true
@[expose] public section
public section
open Finset Real Complex
open FixedOrderFactor

theorem P2M_FixedOrderFactor_sum_orbitAvg_mul__4157f1f1226d {s : ℕ} (hs : 0 < s) (c : ℕ) :
    ∑ t ∈ range s, orbitAvg s (c * t) = if s ∣ c then (s : ℂ) else 0 := by sorry

alias «FixedOrderFactor».«sum_orbitAvg_mul'» := P2M_FixedOrderFactor_sum_orbitAvg_mul__4157f1f1226d
