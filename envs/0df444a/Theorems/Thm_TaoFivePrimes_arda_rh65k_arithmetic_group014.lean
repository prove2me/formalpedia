-- Prove2me | Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group014
-- name    : TaoFivePrimes.arda_rh65k_arithmetic_group014
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T02:19:20.334546+00:00
-- url     : https://prove2.me/theorems/4cfc8c7a-ccf8-49d5-a505-0e9c34ee40d8
-- title:
--   Riemann–Siegel arithmetic certificate, group 14
-- statement:
--   For each listed dyadic sample list, the sharp finite integer band checker accepts the list and the stated number of adjacent sign changes. The assertion concerns the Boolean arithmetic checker; its application to zeta zeros requires a separate soundness theorem.
-- source:
--   Finite certificate generated for the Chebyshev target, using the checker in https://github.com/DrMurphyIsIn/Arda/blob/af4fde897/telperion/examples/zeta_reflection/lean/RS5_EvalSharp.lean

import Definitions.Def_ArdaRH65K_Data014

theorem TaoFivePrimes.arda_rh65k_arithmetic_group014 :
    (RS5.bandOK' RH65K_0112.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0112.samples = 127) ∧
    (RS5.bandOK' RH65K_0113.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0113.samples = 127) ∧
    (RS5.bandOK' RH65K_0114.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0114.samples = 127) ∧
    (RS5.bandOK' RH65K_0115.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0115.samples = 127) ∧
    (RS5.bandOK' RH65K_0116.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0116.samples = 127) ∧
    (RS5.bandOK' RH65K_0117.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0117.samples = 127) ∧
    (RS5.bandOK' RH65K_0118.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0118.samples = 127) ∧
    (RS5.bandOK' RH65K_0119.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0119.samples = 127) := by sorry
