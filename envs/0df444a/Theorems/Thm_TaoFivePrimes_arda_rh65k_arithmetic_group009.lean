-- Prove2me | Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group009
-- name    : TaoFivePrimes.arda_rh65k_arithmetic_group009
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T02:10:34.2899+00:00
-- url     : https://prove2.me/theorems/39c2a6f8-3828-4d4a-8cea-25619e4f7f7b
-- title:
--   Riemann–Siegel arithmetic certificate, group 9
-- statement:
--   For each listed dyadic sample list, the sharp finite integer band checker accepts the list and the stated number of adjacent sign changes. The assertion concerns the Boolean arithmetic checker; its application to zeta zeros requires a separate soundness theorem.
-- source:
--   Finite certificate generated for the Chebyshev target, using the checker in https://github.com/DrMurphyIsIn/Arda/blob/af4fde897/telperion/examples/zeta_reflection/lean/RS5_EvalSharp.lean

import Definitions.Def_ArdaRH65K_Data009

theorem TaoFivePrimes.arda_rh65k_arithmetic_group009 :
    (RS5.bandOK' RH65K_0072.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0072.samples = 127) ∧
    (RS5.bandOK' RH65K_0073.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0073.samples = 127) ∧
    (RS5.bandOK' RH65K_0074.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0074.samples = 127) ∧
    (RS5.bandOK' RH65K_0075.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0075.samples = 127) ∧
    (RS5.bandOK' RH65K_0076.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0076.samples = 127) ∧
    (RS5.bandOK' RH65K_0077.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0077.samples = 127) ∧
    (RS5.bandOK' RH65K_0078.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0078.samples = 127) ∧
    (RS5.bandOK' RH65K_0079.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0079.samples = 127) := by sorry
