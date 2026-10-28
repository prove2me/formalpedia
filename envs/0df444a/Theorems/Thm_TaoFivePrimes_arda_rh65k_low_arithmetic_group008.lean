-- Prove2me | Theorems.Thm_TaoFivePrimes_arda_rh65k_low_arithmetic_group008
-- name    : TaoFivePrimes.arda_rh65k_low_arithmetic_group008
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T03:39:14.716873+00:00
-- url     : https://prove2.me/theorems/97301b50-bebc-4bb1-b9b1-407f6af2c5bd
-- title:
--   Riemann–Siegel arithmetic certificate, group 8
-- statement:
--   For each listed dyadic sample list, the finite integer band checker accepts the list and the stated number of adjacent sign changes. The assertion concerns the Boolean arithmetic checker; its application to zeta zeros requires a separate soundness theorem.
-- source:
--   Finite certificate generated for the Chebyshev target, using the checker in https://github.com/DrMurphyIsIn/Arda/blob/af4fde897/telperion/examples/zeta_reflection/lean/RS5_EvalSharp.lean

import Definitions.Def_ArdaRH65K_LowData008

theorem TaoFivePrimes.arda_rh65k_low_arithmetic_group008 :
    (RS5.bandOK' RH65K_Low_0064.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0064.samples = 127) ∧
    (RS5.bandOK' RH65K_Low_0065.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0065.samples = 127) ∧
    (RS5.bandOK' RH65K_Low_0066.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0066.samples = 127) ∧
    (RS5.bandOK' RH65K_Low_0067.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0067.samples = 127) ∧
    (RS5.bandOK' RH65K_Low_0068.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0068.samples = 127) ∧
    (RS5.bandOK' RH65K_Low_0069.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0069.samples = 127) ∧
    (RS5.bandOK' RH65K_Low_0070.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0070.samples = 127) ∧
    (RS5.bandOK' RH65K_Low_0071.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0071.samples = 127) := by sorry
