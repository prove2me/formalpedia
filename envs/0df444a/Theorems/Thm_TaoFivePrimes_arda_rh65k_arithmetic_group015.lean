-- Prove2me | Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group015
-- name    : TaoFivePrimes.arda_rh65k_arithmetic_group015
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T02:22:43.015445+00:00
-- url     : https://prove2.me/theorems/23a88765-3978-4c3d-abc2-f2a9451e7ab7
-- title:
--   Riemann–Siegel arithmetic certificate, group 15
-- statement:
--   For each listed dyadic sample list, the sharp finite integer band checker accepts the list and the stated number of adjacent sign changes. The assertion concerns the Boolean arithmetic checker; its application to zeta zeros requires a separate soundness theorem.
-- source:
--   Finite certificate generated for the Chebyshev target, using the checker in https://github.com/DrMurphyIsIn/Arda/blob/af4fde897/telperion/examples/zeta_reflection/lean/RS5_EvalSharp.lean

import Definitions.Def_ArdaRH65K_Data015

theorem TaoFivePrimes.arda_rh65k_arithmetic_group015 :
    (RS5.bandOK' RH65K_0120.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0120.samples = 127) ∧
    (RS5.bandOK' RH65K_0121.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0121.samples = 127) ∧
    (RS5.bandOK' RH65K_0122.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0122.samples = 127) ∧
    (RS5.bandOK' RH65K_0123.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0123.samples = 127) ∧
    (RS5.bandOK' RH65K_0124.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0124.samples = 127) ∧
    (RS5.bandOK' RH65K_0125.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0125.samples = 127) ∧
    (RS5.bandOK' RH65K_0126.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0126.samples = 127) ∧
    (RS5.bandOK' RH65K_0127.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0127.samples = 127) := by sorry
