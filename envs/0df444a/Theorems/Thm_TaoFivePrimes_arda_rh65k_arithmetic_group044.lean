-- Prove2me | Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group044
-- name    : TaoFivePrimes.arda_rh65k_arithmetic_group044
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T03:31:05.434621+00:00
-- url     : https://prove2.me/theorems/4ec43c27-082e-4cf7-802f-3e51e792a0b8
-- title:
--   Riemann–Siegel arithmetic certificate, group 44
-- statement:
--   For each listed dyadic sample list, the finite integer band checker accepts the list and the stated number of adjacent sign changes. The assertion concerns the Boolean arithmetic checker; its application to zeta zeros requires a separate soundness theorem.
-- source:
--   Finite certificate generated for the Chebyshev target, using the checker in https://github.com/DrMurphyIsIn/Arda/blob/af4fde897/telperion/examples/zeta_reflection/lean/RS5_EvalSharp.lean

import Definitions.Def_ArdaRH65K_Data044

theorem TaoFivePrimes.arda_rh65k_arithmetic_group044 :
    (RS5.bandOK' RH65K_0352.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0352.samples = 127) ∧
    (RS5.bandOK' RH65K_0353.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0353.samples = 127) ∧
    (RS5.bandOK' RH65K_0354.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0354.samples = 127) ∧
    (RS5.bandOK' RH65K_0355.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0355.samples = 127) ∧
    (RS5.bandOK' RH65K_0356.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0356.samples = 127) ∧
    (RS5.bandOK' RH65K_0357.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0357.samples = 127) ∧
    (RS5.bandOK' RH65K_0358.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0358.samples = 127) ∧
    (RS5.bandOK' RH65K_0359.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0359.samples = 127) := by sorry
