-- Prove2me | Theorems.Thm_TaoFivePrimes_arda_rh65k_low_arithmetic_group000
-- name    : TaoFivePrimes.arda_rh65k_low_arithmetic_group000
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T02:59:39.874852+00:00
-- url     : https://prove2.me/theorems/984df614-54e1-40d7-8388-bbc3d93291ec
-- title:
--   Riemann–Siegel arithmetic certificate, group 0
-- statement:
--   For each listed dyadic sample list, the finite integer band checker accepts the list and the stated number of adjacent sign changes. The assertion concerns the Boolean arithmetic checker; its application to zeta zeros requires a separate soundness theorem.
-- source:
--   Finite certificate generated for the Chebyshev target, using the checker in https://github.com/DrMurphyIsIn/Arda/blob/af4fde897/telperion/examples/zeta_reflection/lean/RS5_EvalSharp.lean

import Definitions.Def_ArdaRH65K_LowData000

theorem TaoFivePrimes.arda_rh65k_low_arithmetic_group000 :
    (RS5.bandOK RH65K_Low_0000.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0000.samples = 127) ∧
    (RS5.bandOK RH65K_Low_0001.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0001.samples = 127) ∧
    (RS5.bandOK RH65K_Low_0002.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0002.samples = 127) ∧
    (RS5.bandOK RH65K_Low_0003.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0003.samples = 127) ∧
    (RS5.bandOK RH65K_Low_0004.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0004.samples = 127) ∧
    (RS5.bandOK RH65K_Low_0005.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0005.samples = 127) ∧
    (RS5.bandOK RH65K_Low_0006.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0006.samples = 127) ∧
    (RS5.bandOK RH65K_Low_0007.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0007.samples = 127) := by sorry
