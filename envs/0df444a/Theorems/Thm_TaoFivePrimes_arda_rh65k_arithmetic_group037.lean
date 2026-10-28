-- Prove2me | Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group037
-- name    : TaoFivePrimes.arda_rh65k_arithmetic_group037
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T03:13:52.789482+00:00
-- url     : https://prove2.me/theorems/13f9bd70-739a-4083-8740-6ace0bf2d846
-- title:
--   Riemann–Siegel arithmetic certificate, group 37
-- statement:
--   For each listed dyadic sample list, the finite integer band checker accepts the list and the stated number of adjacent sign changes. The assertion concerns the Boolean arithmetic checker; its application to zeta zeros requires a separate soundness theorem.
-- source:
--   Finite certificate generated for the Chebyshev target, using the checker in https://github.com/DrMurphyIsIn/Arda/blob/af4fde897/telperion/examples/zeta_reflection/lean/RS5_EvalSharp.lean

import Definitions.Def_ArdaRH65K_Data037

theorem TaoFivePrimes.arda_rh65k_arithmetic_group037 :
    (RS5.bandOK' RH65K_0296.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0296.samples = 127) ∧
    (RS5.bandOK' RH65K_0297.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0297.samples = 127) ∧
    (RS5.bandOK' RH65K_0298.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0298.samples = 127) ∧
    (RS5.bandOK' RH65K_0299.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0299.samples = 127) ∧
    (RS5.bandOK' RH65K_0300.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0300.samples = 127) ∧
    (RS5.bandOK' RH65K_0301.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0301.samples = 127) ∧
    (RS5.bandOK' RH65K_0302.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0302.samples = 127) ∧
    (RS5.bandOK' RH65K_0303.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0303.samples = 127) := by sorry
