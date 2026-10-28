-- Prove2me | Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group052
-- name    : TaoFivePrimes.arda_rh65k_arithmetic_group052
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T03:56:05.266395+00:00
-- url     : https://prove2.me/theorems/cd3455eb-28c8-40f5-a7f0-8a4d7b98aea0
-- title:
--   Riemann–Siegel arithmetic certificate, group 52
-- statement:
--   For each listed dyadic sample list, the finite integer band checker accepts the list and the stated number of adjacent sign changes. The assertion concerns the Boolean arithmetic checker; its application to zeta zeros requires a separate soundness theorem.
-- source:
--   Finite certificate generated for the Chebyshev target, using the checker in https://github.com/DrMurphyIsIn/Arda/blob/af4fde897/telperion/examples/zeta_reflection/lean/RS5_EvalSharp.lean

import Definitions.Def_ArdaRH65K_Data052

theorem TaoFivePrimes.arda_rh65k_arithmetic_group052 :
    (RS5.bandOK' RH65K_0416.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0416.samples = 127) ∧
    (RS5.bandOK' RH65K_0417.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0417.samples = 127) ∧
    (RS5.bandOK' RH65K_0418.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0418.samples = 127) ∧
    (RS5.bandOK' RH65K_0419.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0419.samples = 127) ∧
    (RS5.bandOK' RH65K_0420.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0420.samples = 127) ∧
    (RS5.bandOK' RH65K_0421.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0421.samples = 127) ∧
    (RS5.bandOK' RH65K_0422.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0422.samples = 127) ∧
    (RS5.bandOK' RH65K_0423.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0423.samples = 127) := by sorry
