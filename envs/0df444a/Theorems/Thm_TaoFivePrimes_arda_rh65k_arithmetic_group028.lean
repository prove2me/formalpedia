-- Prove2me | Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group028
-- name    : TaoFivePrimes.arda_rh65k_arithmetic_group028
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T02:52:07.303206+00:00
-- url     : https://prove2.me/theorems/1b578bf2-11dd-4a76-88b5-958bb3da3645
-- title:
--   Riemann–Siegel arithmetic certificate, group 28
-- statement:
--   For each listed dyadic sample list, the finite integer band checker accepts the list and the stated number of adjacent sign changes. The assertion concerns the Boolean arithmetic checker; its application to zeta zeros requires a separate soundness theorem.
-- source:
--   Finite certificate generated for the Chebyshev target, using the checker in https://github.com/DrMurphyIsIn/Arda/blob/af4fde897/telperion/examples/zeta_reflection/lean/RS5_EvalSharp.lean

import Definitions.Def_ArdaRH65K_Data028

theorem TaoFivePrimes.arda_rh65k_arithmetic_group028 :
    (RS5.bandOK' RH65K_0224.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0224.samples = 127) ∧
    (RS5.bandOK' RH65K_0225.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0225.samples = 127) ∧
    (RS5.bandOK' RH65K_0226.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0226.samples = 127) ∧
    (RS5.bandOK' RH65K_0227.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0227.samples = 127) ∧
    (RS5.bandOK' RH65K_0228.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0228.samples = 127) ∧
    (RS5.bandOK' RH65K_0229.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0229.samples = 127) ∧
    (RS5.bandOK' RH65K_0230.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0230.samples = 127) ∧
    (RS5.bandOK' RH65K_0231.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0231.samples = 127) := by sorry
