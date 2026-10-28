-- Prove2me | Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group050
-- name    : TaoFivePrimes.arda_rh65k_arithmetic_group050
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T03:51:02.453433+00:00
-- url     : https://prove2.me/theorems/a4ae9a50-8df2-4d73-8a35-54c4c269e644
-- title:
--   Riemann–Siegel arithmetic certificate, group 50
-- statement:
--   For each listed dyadic sample list, the finite integer band checker accepts the list and the stated number of adjacent sign changes. The assertion concerns the Boolean arithmetic checker; its application to zeta zeros requires a separate soundness theorem.
-- source:
--   Finite certificate generated for the Chebyshev target, using the checker in https://github.com/DrMurphyIsIn/Arda/blob/af4fde897/telperion/examples/zeta_reflection/lean/RS5_EvalSharp.lean

import Definitions.Def_ArdaRH65K_Data050

theorem TaoFivePrimes.arda_rh65k_arithmetic_group050 :
    (RS5.bandOK' RH65K_0400.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0400.samples = 127) ∧
    (RS5.bandOK' RH65K_0401.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0401.samples = 127) ∧
    (RS5.bandOK' RH65K_0402.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0402.samples = 127) ∧
    (RS5.bandOK' RH65K_0403.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0403.samples = 127) ∧
    (RS5.bandOK' RH65K_0404.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0404.samples = 127) ∧
    (RS5.bandOK' RH65K_0405.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0405.samples = 127) ∧
    (RS5.bandOK' RH65K_0406.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0406.samples = 127) ∧
    (RS5.bandOK' RH65K_0407.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0407.samples = 127) := by sorry
