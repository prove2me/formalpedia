-- Prove2me | Theorems.Thm_TaoFivePrimes_arda_rh65k_bridge_arithmetic_group000
-- name    : TaoFivePrimes.arda_rh65k_bridge_arithmetic_group000
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:08:05.139128+00:00
-- url     : https://prove2.me/theorems/bcfa5f62-200e-444a-bd80-00575c48e7fd
-- title:
--   Arithmetic checks for the 520-to-1000 sample bridge
-- statement:
--   For the three recorded sample lists, the finite integer band checker succeeds and the respective adjacent sign-change counts are
--
--   $$(c_0,c_1,c_2)=(127,127,112).$$
--
--   This is an arithmetic statement about the checker. Turning these checks into zeros of the Riemann zeta function requires a separate analytic soundness theorem.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/RS5_Eval.lean#L130-L158

import Definitions.Def_ArdaRH65K_BridgeData000

theorem TaoFivePrimes.arda_rh65k_bridge_arithmetic_group000 :
    (RS5.bandOK RH65K_Bridge_0000.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Bridge_0000.samples = 127) ∧
    (RS5.bandOK RH65K_Bridge_0001.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Bridge_0001.samples = 127) ∧
    (RS5.bandOK RH65K_Bridge_0002.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Bridge_0002.samples = 112) := by sorry
