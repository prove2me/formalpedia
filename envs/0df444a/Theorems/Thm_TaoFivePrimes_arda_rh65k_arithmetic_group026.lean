-- Prove2me | Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group026
-- name    : TaoFivePrimes.arda_rh65k_arithmetic_group026
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T02:46:57.742361+00:00
-- url     : https://prove2.me/theorems/f1f3f8a7-d502-4862-8c4b-cb1de89521cd
-- title:
--   Riemann–Siegel arithmetic certificate, group 26
-- statement:
--   For each listed dyadic sample list, the sharp finite integer band checker accepts the list and the stated number of adjacent sign changes. The assertion concerns the Boolean arithmetic checker; its application to zeta zeros requires a separate soundness theorem.
-- source:
--   Finite certificate generated for the Chebyshev target, using the checker in https://github.com/DrMurphyIsIn/Arda/blob/af4fde897/telperion/examples/zeta_reflection/lean/RS5_EvalSharp.lean

import Definitions.Def_ArdaRH65K_Data026

theorem TaoFivePrimes.arda_rh65k_arithmetic_group026 :
    (RS5.bandOK' RH65K_0208.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0208.samples = 127) ∧
    (RS5.bandOK' RH65K_0209.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0209.samples = 127) ∧
    (RS5.bandOK' RH65K_0210.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0210.samples = 127) ∧
    (RS5.bandOK' RH65K_0211.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0211.samples = 127) ∧
    (RS5.bandOK' RH65K_0212.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0212.samples = 127) ∧
    (RS5.bandOK' RH65K_0213.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0213.samples = 127) ∧
    (RS5.bandOK' RH65K_0214.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0214.samples = 127) ∧
    (RS5.bandOK' RH65K_0215.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0215.samples = 127) := by sorry
