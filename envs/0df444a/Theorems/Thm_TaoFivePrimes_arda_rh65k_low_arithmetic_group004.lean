-- Prove2me | Theorems.Thm_TaoFivePrimes_arda_rh65k_low_arithmetic_group004
-- name    : TaoFivePrimes.arda_rh65k_low_arithmetic_group004
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T03:24:22.516527+00:00
-- url     : https://prove2.me/theorems/f3ad7a39-9ca6-4e20-aaba-37e712a19cdb
-- title:
--   Riemann–Siegel arithmetic certificate, group 4
-- statement:
--   For each listed dyadic sample list, the finite integer band checker accepts the list and the stated number of adjacent sign changes. The assertion concerns the Boolean arithmetic checker; its application to zeta zeros requires a separate soundness theorem.
-- source:
--   Finite certificate generated for the Chebyshev target, using the checker in https://github.com/DrMurphyIsIn/Arda/blob/af4fde897/telperion/examples/zeta_reflection/lean/RS5_EvalSharp.lean

import Definitions.Def_ArdaRH65K_LowData004

theorem TaoFivePrimes.arda_rh65k_low_arithmetic_group004 :
    (RS5.bandOK' RH65K_Low_0032.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0032.samples = 127) ∧
    (RS5.bandOK' RH65K_Low_0033.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0033.samples = 127) ∧
    (RS5.bandOK' RH65K_Low_0034.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0034.samples = 127) ∧
    (RS5.bandOK' RH65K_Low_0035.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0035.samples = 127) ∧
    (RS5.bandOK' RH65K_Low_0036.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0036.samples = 127) ∧
    (RS5.bandOK' RH65K_Low_0037.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0037.samples = 127) ∧
    (RS5.bandOK' RH65K_Low_0038.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0038.samples = 127) ∧
    (RS5.bandOK' RH65K_Low_0039.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0039.samples = 127) := by sorry
