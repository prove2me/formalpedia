-- Prove2me | Theorems.Thm_TaoFivePrimes_arda_rh65k_low_arithmetic_group009
-- name    : TaoFivePrimes.arda_rh65k_low_arithmetic_group009
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T03:43:18.564797+00:00
-- url     : https://prove2.me/theorems/e4917a0a-562a-4039-86f9-3615192dfc3c
-- title:
--   Riemann–Siegel arithmetic certificate, group 9
-- statement:
--   For each listed dyadic sample list, the finite integer band checker accepts the list and the stated number of adjacent sign changes. The assertion concerns the Boolean arithmetic checker; its application to zeta zeros requires a separate soundness theorem.
-- source:
--   Finite certificate generated for the Chebyshev target, using the checker in https://github.com/DrMurphyIsIn/Arda/blob/af4fde897/telperion/examples/zeta_reflection/lean/RS5_EvalSharp.lean

import Definitions.Def_ArdaRH65K_LowData009

theorem TaoFivePrimes.arda_rh65k_low_arithmetic_group009 :
    (RS5.bandOK' RH65K_Low_0072.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0072.samples = 127) ∧
    (RS5.bandOK' RH65K_Low_0073.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0073.samples = 127) ∧
    (RS5.bandOK' RH65K_Low_0074.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0074.samples = 127) ∧
    (RS5.bandOK' RH65K_Low_0075.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0075.samples = 127) ∧
    (RS5.bandOK' RH65K_Low_0076.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0076.samples = 127) ∧
    (RS5.bandOK' RH65K_Low_0077.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0077.samples = 127) ∧
    (RS5.bandOK' RH65K_Low_0078.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0078.samples = 127) ∧
    (RS5.bandOK' RH65K_Low_0079.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0079.samples = 127) := by sorry
