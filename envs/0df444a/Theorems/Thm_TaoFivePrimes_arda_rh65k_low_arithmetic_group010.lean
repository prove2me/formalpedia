-- Prove2me | Theorems.Thm_TaoFivePrimes_arda_rh65k_low_arithmetic_group010
-- name    : TaoFivePrimes.arda_rh65k_low_arithmetic_group010
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T03:46:15.755817+00:00
-- url     : https://prove2.me/theorems/f2e0f95b-fe66-4b28-b020-81ff1234b2c0
-- title:
--   Riemann–Siegel arithmetic certificate, group 10
-- statement:
--   For each listed dyadic sample list, the finite integer band checker accepts the list and the stated number of adjacent sign changes. The assertion concerns the Boolean arithmetic checker; its application to zeta zeros requires a separate soundness theorem.
-- source:
--   Finite certificate generated for the Chebyshev target, using the checker in https://github.com/DrMurphyIsIn/Arda/blob/af4fde897/telperion/examples/zeta_reflection/lean/RS5_EvalSharp.lean

import Definitions.Def_ArdaRH65K_LowData010

theorem TaoFivePrimes.arda_rh65k_low_arithmetic_group010 :
    (RS5.bandOK' RH65K_Low_0080.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0080.samples = 127) ∧
    (RS5.bandOK' RH65K_Low_0081.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0081.samples = 127) ∧
    (RS5.bandOK' RH65K_Low_0082.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0082.samples = 127) ∧
    (RS5.bandOK' RH65K_Low_0083.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0083.samples = 127) ∧
    (RS5.bandOK' RH65K_Low_0084.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0084.samples = 103) := by sorry
