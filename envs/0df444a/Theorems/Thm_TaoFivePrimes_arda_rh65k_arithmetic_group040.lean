-- Prove2me | Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group040
-- name    : TaoFivePrimes.arda_rh65k_arithmetic_group040
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T03:21:19.198067+00:00
-- url     : https://prove2.me/theorems/945771df-e193-4a79-a315-4064e45717a1
-- title:
--   Riemann–Siegel arithmetic certificate, group 40
-- statement:
--   For each listed dyadic sample list, the finite integer band checker accepts the list and the stated number of adjacent sign changes. The assertion concerns the Boolean arithmetic checker; its application to zeta zeros requires a separate soundness theorem.
-- source:
--   Finite certificate generated for the Chebyshev target, using the checker in https://github.com/DrMurphyIsIn/Arda/blob/af4fde897/telperion/examples/zeta_reflection/lean/RS5_EvalSharp.lean

import Definitions.Def_ArdaRH65K_Data040

theorem TaoFivePrimes.arda_rh65k_arithmetic_group040 :
    (RS5.bandOK' RH65K_0320.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0320.samples = 127) ∧
    (RS5.bandOK' RH65K_0321.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0321.samples = 127) ∧
    (RS5.bandOK' RH65K_0322.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0322.samples = 127) ∧
    (RS5.bandOK' RH65K_0323.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0323.samples = 127) ∧
    (RS5.bandOK' RH65K_0324.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0324.samples = 127) ∧
    (RS5.bandOK' RH65K_0325.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0325.samples = 127) ∧
    (RS5.bandOK' RH65K_0326.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0326.samples = 127) ∧
    (RS5.bandOK' RH65K_0327.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0327.samples = 127) := by sorry
