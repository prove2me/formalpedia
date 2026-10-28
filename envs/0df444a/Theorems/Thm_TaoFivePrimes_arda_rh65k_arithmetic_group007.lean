-- Prove2me | Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group007
-- name    : TaoFivePrimes.arda_rh65k_arithmetic_group007
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T02:06:34.4883+00:00
-- url     : https://prove2.me/theorems/96560ba2-1890-4acd-b7f7-3eed7bc9f786
-- title:
--   Riemann–Siegel arithmetic certificate, group 7
-- statement:
--   For each listed dyadic sample list, the sharp finite integer band checker accepts the list and the stated number of adjacent sign changes. The assertion concerns the Boolean arithmetic checker; its application to zeta zeros requires a separate soundness theorem.
-- source:
--   Finite certificate generated for the Chebyshev target, using the checker in https://github.com/DrMurphyIsIn/Arda/blob/af4fde897/telperion/examples/zeta_reflection/lean/RS5_EvalSharp.lean

import Definitions.Def_ArdaRH65K_Data007

theorem TaoFivePrimes.arda_rh65k_arithmetic_group007 :
    (RS5.bandOK' RH65K_0056.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0056.samples = 127) ∧
    (RS5.bandOK' RH65K_0057.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0057.samples = 127) ∧
    (RS5.bandOK' RH65K_0058.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0058.samples = 127) ∧
    (RS5.bandOK' RH65K_0059.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0059.samples = 127) ∧
    (RS5.bandOK' RH65K_0060.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0060.samples = 127) ∧
    (RS5.bandOK' RH65K_0061.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0061.samples = 127) ∧
    (RS5.bandOK' RH65K_0062.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0062.samples = 127) ∧
    (RS5.bandOK' RH65K_0063.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0063.samples = 127) := by sorry
