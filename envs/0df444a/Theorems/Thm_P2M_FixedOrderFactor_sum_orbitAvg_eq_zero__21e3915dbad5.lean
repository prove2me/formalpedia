-- Prove2me | Theorems.Thm_P2M_FixedOrderFactor_sum_orbitAvg_eq_zero__21e3915dbad5
-- name    : P2M_FixedOrderFactor_sum_orbitAvg_eq_zero__21e3915dbad5
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:55:44.493938+00:00
-- url     : https://prove2.me/theorems/cb6571be-ef54-592a-ade8-fd66d5a4a056
-- title:
--   P2 M Fixed Order Factor sum orbit Avg eq zero  21e3915dbad5: P2 M Fixed Order Factor sum orbit Avg eq zero  21e3915dbad5
-- statement:
--   The class function has mean zero: `∑_{t<s} ϱ_s(t) = 0` for `s > 1`.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Bias.lean#L81-L87
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Bias.lean#L81-L87

module
public import Definitions.Def_FixedOrderFactor_Local
public import Definitions.Def_FixedOrderFactor_Bias
set_option autoImplicit true
@[expose] public section
public section
open Finset Real Complex
open FixedOrderFactor

theorem P2M_FixedOrderFactor_sum_orbitAvg_eq_zero__21e3915dbad5 {s : ℕ} (hs : 1 < s) : ∑ t ∈ range s, orbitAvg s t = 0 := by sorry

alias «FixedOrderFactor».«sum_orbitAvg_eq_zero'» := P2M_FixedOrderFactor_sum_orbitAvg_eq_zero__21e3915dbad5
