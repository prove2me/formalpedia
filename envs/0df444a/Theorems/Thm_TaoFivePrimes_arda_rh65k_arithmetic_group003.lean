-- Prove2me | Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group003
-- name    : TaoFivePrimes.arda_rh65k_arithmetic_group003
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T01:59:03.735215+00:00
-- url     : https://prove2.me/theorems/78b30c4e-b386-4b1e-b87d-03fda8db60e9
-- title:
--   Riemann–Siegel arithmetic certificate, group 3
-- statement:
--   For each listed dyadic sample list, the sharp finite integer band checker accepts the list and the stated number of adjacent sign changes. The assertion concerns the Boolean arithmetic checker; its application to zeta zeros requires a separate soundness theorem.
-- source:
--   Finite certificate generated for the Chebyshev target, using the checker in https://github.com/DrMurphyIsIn/Arda/blob/af4fde897/telperion/examples/zeta_reflection/lean/RS5_EvalSharp.lean

import Definitions.Def_ArdaRH65K_Data003

theorem TaoFivePrimes.arda_rh65k_arithmetic_group003 :
    (RS5.bandOK' RH65K_0024.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0024.samples = 127) ∧
    (RS5.bandOK' RH65K_0025.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0025.samples = 127) ∧
    (RS5.bandOK' RH65K_0026.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0026.samples = 127) ∧
    (RS5.bandOK' RH65K_0027.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0027.samples = 127) ∧
    (RS5.bandOK' RH65K_0028.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0028.samples = 127) ∧
    (RS5.bandOK' RH65K_0029.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0029.samples = 127) ∧
    (RS5.bandOK' RH65K_0030.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0030.samples = 127) ∧
    (RS5.bandOK' RH65K_0031.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0031.samples = 127) := by sorry
