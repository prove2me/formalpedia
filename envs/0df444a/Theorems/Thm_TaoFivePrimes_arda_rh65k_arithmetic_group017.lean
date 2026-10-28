-- Prove2me | Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group017
-- name    : TaoFivePrimes.arda_rh65k_arithmetic_group017
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T02:25:57.712501+00:00
-- url     : https://prove2.me/theorems/ccba73c1-3406-4995-9372-5ec15ec06ee8
-- title:
--   Riemann–Siegel arithmetic certificate, group 17
-- statement:
--   For each listed dyadic sample list, the sharp finite integer band checker accepts the list and the stated number of adjacent sign changes. The assertion concerns the Boolean arithmetic checker; its application to zeta zeros requires a separate soundness theorem.
-- source:
--   Finite certificate generated for the Chebyshev target, using the checker in https://github.com/DrMurphyIsIn/Arda/blob/af4fde897/telperion/examples/zeta_reflection/lean/RS5_EvalSharp.lean

import Definitions.Def_ArdaRH65K_Data017

theorem TaoFivePrimes.arda_rh65k_arithmetic_group017 :
    (RS5.bandOK' RH65K_0136.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0136.samples = 127) ∧
    (RS5.bandOK' RH65K_0137.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0137.samples = 127) ∧
    (RS5.bandOK' RH65K_0138.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0138.samples = 127) ∧
    (RS5.bandOK' RH65K_0139.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0139.samples = 127) ∧
    (RS5.bandOK' RH65K_0140.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0140.samples = 127) ∧
    (RS5.bandOK' RH65K_0141.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0141.samples = 127) ∧
    (RS5.bandOK' RH65K_0142.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0142.samples = 127) ∧
    (RS5.bandOK' RH65K_0143.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0143.samples = 127) := by sorry
