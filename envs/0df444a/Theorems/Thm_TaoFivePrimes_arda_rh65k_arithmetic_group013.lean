-- Prove2me | Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group013
-- name    : TaoFivePrimes.arda_rh65k_arithmetic_group013
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T02:18:12.455664+00:00
-- url     : https://prove2.me/theorems/1740a687-fa83-43ae-9fe1-ae3ba6a697a4
-- title:
--   Riemann–Siegel arithmetic certificate, group 13
-- statement:
--   For each listed dyadic sample list, the sharp finite integer band checker accepts the list and the stated number of adjacent sign changes. The assertion concerns the Boolean arithmetic checker; its application to zeta zeros requires a separate soundness theorem.
-- source:
--   Finite certificate generated for the Chebyshev target, using the checker in https://github.com/DrMurphyIsIn/Arda/blob/af4fde897/telperion/examples/zeta_reflection/lean/RS5_EvalSharp.lean

import Definitions.Def_ArdaRH65K_Data013

theorem TaoFivePrimes.arda_rh65k_arithmetic_group013 :
    (RS5.bandOK' RH65K_0104.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0104.samples = 127) ∧
    (RS5.bandOK' RH65K_0105.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0105.samples = 127) ∧
    (RS5.bandOK' RH65K_0106.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0106.samples = 127) ∧
    (RS5.bandOK' RH65K_0107.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0107.samples = 127) ∧
    (RS5.bandOK' RH65K_0108.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0108.samples = 127) ∧
    (RS5.bandOK' RH65K_0109.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0109.samples = 127) ∧
    (RS5.bandOK' RH65K_0110.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0110.samples = 127) ∧
    (RS5.bandOK' RH65K_0111.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0111.samples = 127) := by sorry
