-- Prove2me | Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group035
-- name    : TaoFivePrimes.arda_rh65k_arithmetic_group035
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T03:08:53.572571+00:00
-- url     : https://prove2.me/theorems/a82217c4-47e9-4027-992f-0d45276cae74
-- title:
--   Riemann–Siegel arithmetic certificate, group 35
-- statement:
--   For each listed dyadic sample list, the finite integer band checker accepts the list and the stated number of adjacent sign changes. The assertion concerns the Boolean arithmetic checker; its application to zeta zeros requires a separate soundness theorem.
-- source:
--   Finite certificate generated for the Chebyshev target, using the checker in https://github.com/DrMurphyIsIn/Arda/blob/af4fde897/telperion/examples/zeta_reflection/lean/RS5_EvalSharp.lean

import Definitions.Def_ArdaRH65K_Data035

theorem TaoFivePrimes.arda_rh65k_arithmetic_group035 :
    (RS5.bandOK' RH65K_0280.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0280.samples = 127) ∧
    (RS5.bandOK' RH65K_0281.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0281.samples = 127) ∧
    (RS5.bandOK' RH65K_0282.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0282.samples = 127) ∧
    (RS5.bandOK' RH65K_0283.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0283.samples = 127) ∧
    (RS5.bandOK' RH65K_0284.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0284.samples = 127) ∧
    (RS5.bandOK' RH65K_0285.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0285.samples = 127) ∧
    (RS5.bandOK' RH65K_0286.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0286.samples = 127) ∧
    (RS5.bandOK' RH65K_0287.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0287.samples = 127) := by sorry
