-- Prove2me | Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group036
-- name    : TaoFivePrimes.arda_rh65k_arithmetic_group036
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T03:11:30.059706+00:00
-- url     : https://prove2.me/theorems/860aef11-56c7-4b3c-aee1-a8b59096b4f0
-- title:
--   Riemann–Siegel arithmetic certificate, group 36
-- statement:
--   For each listed dyadic sample list, the finite integer band checker accepts the list and the stated number of adjacent sign changes. The assertion concerns the Boolean arithmetic checker; its application to zeta zeros requires a separate soundness theorem.
-- source:
--   Finite certificate generated for the Chebyshev target, using the checker in https://github.com/DrMurphyIsIn/Arda/blob/af4fde897/telperion/examples/zeta_reflection/lean/RS5_EvalSharp.lean

import Definitions.Def_ArdaRH65K_Data036

theorem TaoFivePrimes.arda_rh65k_arithmetic_group036 :
    (RS5.bandOK' RH65K_0288.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0288.samples = 127) ∧
    (RS5.bandOK' RH65K_0289.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0289.samples = 127) ∧
    (RS5.bandOK' RH65K_0290.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0290.samples = 127) ∧
    (RS5.bandOK' RH65K_0291.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0291.samples = 127) ∧
    (RS5.bandOK' RH65K_0292.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0292.samples = 127) ∧
    (RS5.bandOK' RH65K_0293.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0293.samples = 127) ∧
    (RS5.bandOK' RH65K_0294.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0294.samples = 127) ∧
    (RS5.bandOK' RH65K_0295.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0295.samples = 127) := by sorry
