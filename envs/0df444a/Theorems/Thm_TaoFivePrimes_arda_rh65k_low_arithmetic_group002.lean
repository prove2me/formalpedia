-- Prove2me | Theorems.Thm_TaoFivePrimes_arda_rh65k_low_arithmetic_group002
-- name    : TaoFivePrimes.arda_rh65k_low_arithmetic_group002
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T03:15:42.305881+00:00
-- url     : https://prove2.me/theorems/cc4e7da3-9376-4182-9f62-605163bb54db
-- title:
--   Riemann–Siegel arithmetic certificate, group 2
-- statement:
--   For each listed dyadic sample list, the finite integer band checker accepts the list and the stated number of adjacent sign changes. The assertion concerns the Boolean arithmetic checker; its application to zeta zeros requires a separate soundness theorem.
-- source:
--   Finite certificate generated for the Chebyshev target, using the checker in https://github.com/DrMurphyIsIn/Arda/blob/af4fde897/telperion/examples/zeta_reflection/lean/RS5_EvalSharp.lean

import Definitions.Def_ArdaRH65K_LowData002

theorem TaoFivePrimes.arda_rh65k_low_arithmetic_group002 :
    (RS5.bandOK RH65K_Low_0016.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0016.samples = 127) ∧
    (RS5.bandOK RH65K_Low_0017.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0017.samples = 127) ∧
    (RS5.bandOK RH65K_Low_0018.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0018.samples = 127) ∧
    (RS5.bandOK RH65K_Low_0019.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0019.samples = 127) ∧
    (RS5.bandOK RH65K_Low_0020.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0020.samples = 127) ∧
    (RS5.bandOK RH65K_Low_0021.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0021.samples = 127) ∧
    (RS5.bandOK RH65K_Low_0022.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0022.samples = 127) ∧
    (RS5.bandOK RH65K_Low_0023.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0023.samples = 127) := by sorry
