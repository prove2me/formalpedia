-- Prove2me | Theorems.Thm_TaoFivePrimes_arda_rh65k_low_arithmetic_group001
-- name    : TaoFivePrimes.arda_rh65k_low_arithmetic_group001
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T03:09:08.772475+00:00
-- url     : https://prove2.me/theorems/22ea3059-cfea-4eba-b897-f206b8e848ab
-- title:
--   Riemann–Siegel arithmetic certificate, group 1
-- statement:
--   For each listed dyadic sample list, the finite integer band checker accepts the list and the stated number of adjacent sign changes. The assertion concerns the Boolean arithmetic checker; its application to zeta zeros requires a separate soundness theorem.
-- source:
--   Finite certificate generated for the Chebyshev target, using the checker in https://github.com/DrMurphyIsIn/Arda/blob/af4fde897/telperion/examples/zeta_reflection/lean/RS5_EvalSharp.lean

import Definitions.Def_ArdaRH65K_LowData001

theorem TaoFivePrimes.arda_rh65k_low_arithmetic_group001 :
    (RS5.bandOK RH65K_Low_0008.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0008.samples = 127) ∧
    (RS5.bandOK RH65K_Low_0009.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0009.samples = 127) ∧
    (RS5.bandOK RH65K_Low_0010.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0010.samples = 127) ∧
    (RS5.bandOK RH65K_Low_0011.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0011.samples = 127) ∧
    (RS5.bandOK RH65K_Low_0012.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0012.samples = 127) ∧
    (RS5.bandOK RH65K_Low_0013.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0013.samples = 127) ∧
    (RS5.bandOK RH65K_Low_0014.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0014.samples = 127) ∧
    (RS5.bandOK RH65K_Low_0015.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0015.samples = 127) := by sorry
