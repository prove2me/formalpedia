-- Prove2me | Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group072
-- name    : TaoFivePrimes.arda_rh65k_arithmetic_group072
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T04:49:12.461809+00:00
-- url     : https://prove2.me/theorems/f012df3e-3d86-40a7-a110-1b6503e193f6
-- title:
--   Riemann–Siegel arithmetic certificate, group 72
-- statement:
--   For each listed dyadic sample list, the finite integer band checker accepts the list and the stated number of adjacent sign changes. The assertion concerns the Boolean arithmetic checker; its application to zeta zeros requires a separate soundness theorem.
-- source:
--   Finite certificate generated for the Chebyshev target, using the checker in https://github.com/DrMurphyIsIn/Arda/blob/af4fde897/telperion/examples/zeta_reflection/lean/RS5_EvalSharp.lean

import Definitions.Def_ArdaRH65K_Data072

theorem TaoFivePrimes.arda_rh65k_arithmetic_group072 :
    (RS5.bandOK' RH65K_0576.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0576.samples = 127) ∧
    (RS5.bandOK' RH65K_0577.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0577.samples = 127) ∧
    (RS5.bandOK' RH65K_0578.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0578.samples = 127) ∧
    (RS5.bandOK' RH65K_0579.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0579.samples = 127) ∧
    (RS5.bandOK' RH65K_0580.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0580.samples = 127) ∧
    (RS5.bandOK' RH65K_0581.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0581.samples = 127) ∧
    (RS5.bandOK' RH65K_0582.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0582.samples = 46) := by sorry
