-- Prove2me | Theorems.Thm_P2M_FixedOrderFactor_tendsto_muAvg__0f3103de6ec7
-- name    : P2M_FixedOrderFactor_tendsto_muAvg__0f3103de6ec7
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:51:27.623487+00:00
-- url     : https://prove2.me/theorems/be15e66b-8287-4108-aa8d-71e8bf398edd
-- title:
--   P2 M Fixed Order Factor tendsto mu Avg  0f3103de6ec7: P2 M Fixed Order Factor tendsto mu Avg  0f3103de6ec7
-- statement:
--   The P2 M Fixed Order Factor tendsto mu Avg  0f3103de6ec7 construction uses the P2 M Fixed Order Factor tendsto mu Avg  0f3103de6ec7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Model.lean#L11-L25
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Model.lean#L11-L25

module
public import Definitions.Def_FixedOrderFactor_Euler
public import Definitions.Def_FixedOrderFactor_Local
public import Definitions.Def_FixedOrderFactor_Model
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor

theorem P2M_FixedOrderFactor_tendsto_muAvg__0f3103de6ec7 {x : ℝ} (hx : |x| < 1) :
    Tendsto (fun r => muAvg r x) atTop (𝓝 (1 / (1 - x ^ 2))) := by sorry

alias «FixedOrderFactor».«tendsto_muAvg'» := P2M_FixedOrderFactor_tendsto_muAvg__0f3103de6ec7
