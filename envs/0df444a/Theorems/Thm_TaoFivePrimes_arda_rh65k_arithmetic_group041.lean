-- Prove2me | Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group041
-- name    : TaoFivePrimes.arda_rh65k_arithmetic_group041
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T03:23:22.874384+00:00
-- url     : https://prove2.me/theorems/aae5cf95-8944-4a6b-9b5c-e26fa94cf662
-- title:
--   Riemann–Siegel arithmetic certificate, group 41
-- statement:
--   For each listed dyadic sample list, the finite integer band checker accepts the list and the stated number of adjacent sign changes. The assertion concerns the Boolean arithmetic checker; its application to zeta zeros requires a separate soundness theorem.
-- source:
--   Finite certificate generated for the Chebyshev target, using the checker in https://github.com/DrMurphyIsIn/Arda/blob/af4fde897/telperion/examples/zeta_reflection/lean/RS5_EvalSharp.lean

import Definitions.Def_ArdaRH65K_Data041

theorem TaoFivePrimes.arda_rh65k_arithmetic_group041 :
    (RS5.bandOK' RH65K_0328.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0328.samples = 127) ∧
    (RS5.bandOK' RH65K_0329.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0329.samples = 127) ∧
    (RS5.bandOK' RH65K_0330.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0330.samples = 127) ∧
    (RS5.bandOK' RH65K_0331.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0331.samples = 127) ∧
    (RS5.bandOK' RH65K_0332.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0332.samples = 127) ∧
    (RS5.bandOK' RH65K_0333.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0333.samples = 127) ∧
    (RS5.bandOK' RH65K_0334.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0334.samples = 127) ∧
    (RS5.bandOK' RH65K_0335.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0335.samples = 127) := by sorry
