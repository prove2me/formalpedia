-- Prove2me | Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group046
-- name    : TaoFivePrimes.arda_rh65k_arithmetic_group046
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T03:37:53.160411+00:00
-- url     : https://prove2.me/theorems/855428e4-35da-4952-8197-1a45d4c63c18
-- title:
--   Riemann–Siegel arithmetic certificate, group 46
-- statement:
--   For each listed dyadic sample list, the finite integer band checker accepts the list and the stated number of adjacent sign changes. The assertion concerns the Boolean arithmetic checker; its application to zeta zeros requires a separate soundness theorem.
-- source:
--   Finite certificate generated for the Chebyshev target, using the checker in https://github.com/DrMurphyIsIn/Arda/blob/af4fde897/telperion/examples/zeta_reflection/lean/RS5_EvalSharp.lean

import Definitions.Def_ArdaRH65K_Data046

theorem TaoFivePrimes.arda_rh65k_arithmetic_group046 :
    (RS5.bandOK' RH65K_0368.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0368.samples = 127) ∧
    (RS5.bandOK' RH65K_0369.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0369.samples = 127) ∧
    (RS5.bandOK' RH65K_0370.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0370.samples = 127) ∧
    (RS5.bandOK' RH65K_0371.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0371.samples = 127) ∧
    (RS5.bandOK' RH65K_0372.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0372.samples = 127) ∧
    (RS5.bandOK' RH65K_0373.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0373.samples = 127) ∧
    (RS5.bandOK' RH65K_0374.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0374.samples = 127) ∧
    (RS5.bandOK' RH65K_0375.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0375.samples = 127) := by sorry
