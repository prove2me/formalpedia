-- Prove2me | Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group027
-- name    : TaoFivePrimes.arda_rh65k_arithmetic_group027
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T02:49:47.300564+00:00
-- url     : https://prove2.me/theorems/73f1779d-228c-4f11-8b49-dc334a626d4e
-- title:
--   Riemann–Siegel arithmetic certificate, group 27
-- statement:
--   For each listed dyadic sample list, the sharp finite integer band checker accepts the list and the stated number of adjacent sign changes. The assertion concerns the Boolean arithmetic checker; its application to zeta zeros requires a separate soundness theorem.
-- source:
--   Finite certificate generated for the Chebyshev target, using the checker in https://github.com/DrMurphyIsIn/Arda/blob/af4fde897/telperion/examples/zeta_reflection/lean/RS5_EvalSharp.lean

import Definitions.Def_ArdaRH65K_Data027

theorem TaoFivePrimes.arda_rh65k_arithmetic_group027 :
    (RS5.bandOK' RH65K_0216.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0216.samples = 127) ∧
    (RS5.bandOK' RH65K_0217.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0217.samples = 127) ∧
    (RS5.bandOK' RH65K_0218.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0218.samples = 127) ∧
    (RS5.bandOK' RH65K_0219.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0219.samples = 127) ∧
    (RS5.bandOK' RH65K_0220.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0220.samples = 127) ∧
    (RS5.bandOK' RH65K_0221.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0221.samples = 127) ∧
    (RS5.bandOK' RH65K_0222.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0222.samples = 127) ∧
    (RS5.bandOK' RH65K_0223.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0223.samples = 127) := by sorry
