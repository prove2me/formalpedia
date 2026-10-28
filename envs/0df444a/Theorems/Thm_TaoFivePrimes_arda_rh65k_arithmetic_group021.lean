-- Prove2me | Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group021
-- name    : TaoFivePrimes.arda_rh65k_arithmetic_group021
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T02:34:52.288839+00:00
-- url     : https://prove2.me/theorems/21612f70-2b41-4fc6-9ce3-0ced8f8d0508
-- title:
--   Riemann–Siegel arithmetic certificate, group 21
-- statement:
--   For each listed dyadic sample list, the sharp finite integer band checker accepts the list and the stated number of adjacent sign changes. The assertion concerns the Boolean arithmetic checker; its application to zeta zeros requires a separate soundness theorem.
-- source:
--   Finite certificate generated for the Chebyshev target, using the checker in https://github.com/DrMurphyIsIn/Arda/blob/af4fde897/telperion/examples/zeta_reflection/lean/RS5_EvalSharp.lean

import Definitions.Def_ArdaRH65K_Data021

theorem TaoFivePrimes.arda_rh65k_arithmetic_group021 :
    (RS5.bandOK' RH65K_0168.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0168.samples = 127) ∧
    (RS5.bandOK' RH65K_0169.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0169.samples = 127) ∧
    (RS5.bandOK' RH65K_0170.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0170.samples = 127) ∧
    (RS5.bandOK' RH65K_0171.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0171.samples = 127) ∧
    (RS5.bandOK' RH65K_0172.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0172.samples = 127) ∧
    (RS5.bandOK' RH65K_0173.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0173.samples = 127) ∧
    (RS5.bandOK' RH65K_0174.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0174.samples = 127) ∧
    (RS5.bandOK' RH65K_0175.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0175.samples = 127) := by sorry
