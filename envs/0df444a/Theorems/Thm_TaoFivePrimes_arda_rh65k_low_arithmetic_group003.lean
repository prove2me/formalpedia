-- Prove2me | Theorems.Thm_TaoFivePrimes_arda_rh65k_low_arithmetic_group003
-- name    : TaoFivePrimes.arda_rh65k_low_arithmetic_group003
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T03:17:47.233061+00:00
-- url     : https://prove2.me/theorems/51136ae9-eed6-40a1-a674-dfddddd5efe9
-- title:
--   Riemann–Siegel arithmetic certificate, group 3
-- statement:
--   For each listed dyadic sample list, the finite integer band checker accepts the list and the stated number of adjacent sign changes. The assertion concerns the Boolean arithmetic checker; its application to zeta zeros requires a separate soundness theorem.
-- source:
--   Finite certificate generated for the Chebyshev target, using the checker in https://github.com/DrMurphyIsIn/Arda/blob/af4fde897/telperion/examples/zeta_reflection/lean/RS5_EvalSharp.lean

import Definitions.Def_ArdaRH65K_LowData003

theorem TaoFivePrimes.arda_rh65k_low_arithmetic_group003 :
    (RS5.bandOK RH65K_Low_0024.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0024.samples = 36) ∧
    (RS5.bandOK' RH65K_Low_0025.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0025.samples = 127) ∧
    (RS5.bandOK' RH65K_Low_0026.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0026.samples = 127) ∧
    (RS5.bandOK' RH65K_Low_0027.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0027.samples = 127) ∧
    (RS5.bandOK' RH65K_Low_0028.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0028.samples = 127) ∧
    (RS5.bandOK' RH65K_Low_0029.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0029.samples = 127) ∧
    (RS5.bandOK' RH65K_Low_0030.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0030.samples = 127) ∧
    (RS5.bandOK' RH65K_Low_0031.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0031.samples = 127) := by sorry
