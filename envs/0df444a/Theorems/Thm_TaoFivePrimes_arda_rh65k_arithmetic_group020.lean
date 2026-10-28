-- Prove2me | Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group020
-- name    : TaoFivePrimes.arda_rh65k_arithmetic_group020
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T02:32:13.289725+00:00
-- url     : https://prove2.me/theorems/f268d2a4-bf25-4ffa-85b3-79703a1991f2
-- title:
--   Riemann–Siegel arithmetic certificate, group 20
-- statement:
--   For each listed dyadic sample list, the sharp finite integer band checker accepts the list and the stated number of adjacent sign changes. The assertion concerns the Boolean arithmetic checker; its application to zeta zeros requires a separate soundness theorem.
-- source:
--   Finite certificate generated for the Chebyshev target, using the checker in https://github.com/DrMurphyIsIn/Arda/blob/af4fde897/telperion/examples/zeta_reflection/lean/RS5_EvalSharp.lean

import Definitions.Def_ArdaRH65K_Data020

theorem TaoFivePrimes.arda_rh65k_arithmetic_group020 :
    (RS5.bandOK' RH65K_0160.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0160.samples = 127) ∧
    (RS5.bandOK' RH65K_0161.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0161.samples = 127) ∧
    (RS5.bandOK' RH65K_0162.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0162.samples = 127) ∧
    (RS5.bandOK' RH65K_0163.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0163.samples = 127) ∧
    (RS5.bandOK' RH65K_0164.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0164.samples = 127) ∧
    (RS5.bandOK' RH65K_0165.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0165.samples = 127) ∧
    (RS5.bandOK' RH65K_0166.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0166.samples = 127) ∧
    (RS5.bandOK' RH65K_0167.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0167.samples = 127) := by sorry
