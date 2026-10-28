-- Prove2me | Theorems.Thm_TaoFivePrimes_arda_rh65k_low_arithmetic_group005
-- name    : TaoFivePrimes.arda_rh65k_low_arithmetic_group005
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T03:29:28.982884+00:00
-- url     : https://prove2.me/theorems/01017e68-8ccd-4809-94a4-97b85a018690
-- title:
--   Riemann–Siegel arithmetic certificate, group 5
-- statement:
--   For each listed dyadic sample list, the finite integer band checker accepts the list and the stated number of adjacent sign changes. The assertion concerns the Boolean arithmetic checker; its application to zeta zeros requires a separate soundness theorem.
-- source:
--   Finite certificate generated for the Chebyshev target, using the checker in https://github.com/DrMurphyIsIn/Arda/blob/af4fde897/telperion/examples/zeta_reflection/lean/RS5_EvalSharp.lean

import Definitions.Def_ArdaRH65K_LowData005

theorem TaoFivePrimes.arda_rh65k_low_arithmetic_group005 :
    (RS5.bandOK' RH65K_Low_0040.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0040.samples = 127) ∧
    (RS5.bandOK' RH65K_Low_0041.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0041.samples = 127) ∧
    (RS5.bandOK' RH65K_Low_0042.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0042.samples = 127) ∧
    (RS5.bandOK' RH65K_Low_0043.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0043.samples = 127) ∧
    (RS5.bandOK' RH65K_Low_0044.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0044.samples = 127) ∧
    (RS5.bandOK' RH65K_Low_0045.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0045.samples = 127) ∧
    (RS5.bandOK' RH65K_Low_0046.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0046.samples = 127) ∧
    (RS5.bandOK' RH65K_Low_0047.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0047.samples = 127) := by sorry
