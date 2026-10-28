-- Prove2me | Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group002
-- name    : TaoFivePrimes.arda_rh65k_arithmetic_group002
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T01:57:12.533712+00:00
-- url     : https://prove2.me/theorems/865b2786-1c3b-4aa1-939e-f635f6779909
-- title:
--   Riemann–Siegel arithmetic certificate, group 2
-- statement:
--   For each listed dyadic sample list, the sharp finite integer band checker accepts the list and the stated number of adjacent sign changes. The assertion concerns the Boolean arithmetic checker; its application to zeta zeros requires a separate soundness theorem.
-- source:
--   Finite certificate generated for the Chebyshev target, using the checker in https://github.com/DrMurphyIsIn/Arda/blob/af4fde897/telperion/examples/zeta_reflection/lean/RS5_EvalSharp.lean

import Definitions.Def_ArdaRH65K_Data002

theorem TaoFivePrimes.arda_rh65k_arithmetic_group002 :
    (RS5.bandOK' RH65K_0016.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0016.samples = 127) ∧
    (RS5.bandOK' RH65K_0017.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0017.samples = 127) ∧
    (RS5.bandOK' RH65K_0018.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0018.samples = 127) ∧
    (RS5.bandOK' RH65K_0019.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0019.samples = 127) ∧
    (RS5.bandOK' RH65K_0020.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0020.samples = 127) ∧
    (RS5.bandOK' RH65K_0021.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0021.samples = 127) ∧
    (RS5.bandOK' RH65K_0022.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0022.samples = 127) ∧
    (RS5.bandOK' RH65K_0023.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0023.samples = 127) := by sorry
