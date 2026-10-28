-- Prove2me | Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group004
-- name    : TaoFivePrimes.arda_rh65k_arithmetic_group004
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T02:00:32.882675+00:00
-- url     : https://prove2.me/theorems/11c5f14a-7191-429a-beed-74ef6728e774
-- title:
--   Riemann–Siegel arithmetic certificate, group 4
-- statement:
--   For each listed dyadic sample list, the sharp finite integer band checker accepts the list and the stated number of adjacent sign changes. The assertion concerns the Boolean arithmetic checker; its application to zeta zeros requires a separate soundness theorem.
-- source:
--   Finite certificate generated for the Chebyshev target, using the checker in https://github.com/DrMurphyIsIn/Arda/blob/af4fde897/telperion/examples/zeta_reflection/lean/RS5_EvalSharp.lean

import Definitions.Def_ArdaRH65K_Data004

theorem TaoFivePrimes.arda_rh65k_arithmetic_group004 :
    (RS5.bandOK' RH65K_0032.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0032.samples = 127) ∧
    (RS5.bandOK' RH65K_0033.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0033.samples = 127) ∧
    (RS5.bandOK' RH65K_0034.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0034.samples = 127) ∧
    (RS5.bandOK' RH65K_0035.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0035.samples = 127) ∧
    (RS5.bandOK' RH65K_0036.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0036.samples = 127) ∧
    (RS5.bandOK' RH65K_0037.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0037.samples = 127) ∧
    (RS5.bandOK' RH65K_0038.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0038.samples = 127) ∧
    (RS5.bandOK' RH65K_0039.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0039.samples = 127) := by sorry
