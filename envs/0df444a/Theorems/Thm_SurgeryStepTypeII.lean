-- Prove2me | Theorems.Thm_SurgeryStepTypeII
-- name    : SurgeryStepTypeII
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:14:52.077544+00:00
-- url     : https://prove2.me/theorems/8554c964-d097-4785-a72d-e1a9c15e3cb2
-- title:
--   Surgery Step Type II: Surgery Step Type II
-- statement:
--   The amortization step for a Type II surgery cut (paper.tex 1005-1075, ``Algorithm 1'', Type II
--   branch), isolated as pure real/natural-number arithmetic. Given the numerical output of a Type II
--   cut -- the kept curve's length `L'` and small-edge count `m'`, the discarded curve's length `Ld`,
--   against the input length `L` and small-edge count `m`, subject to `L' ≤ L`,
--   `L' + Ld ≤ L + 4ε⁻¹δ` and `m' + n ≤ m` -- both halves of the induction step follow: the
--   termination measure `M(L,m) = (n+3)⌊L/((1-ε)δ)⌋ + m` drops by at least `n`, and the potential
--   `surgeryPotential` pays for the discarded length.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/SurgeryStepTypeII.lean#L11-L42
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/SurgeryStepTypeII.lean#L11-L42

import Definitions.Def_Tablet_surgeryPotential
import Definitions.Def_Tablet_SurgeryStepTypeII
set_option autoImplicit false

theorem SurgeryStepTypeII (δ ε : ℝ) (n : ℕ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hδ : 0 < δ) (hn : 0 < n) (L L' Ld : ℝ) (m m' : ℕ)
    (hlen : L' ≤ L) (htot : L' + Ld ≤ L + 4 * ε⁻¹ * δ) (hm : m' + n ≤ m) :
    (n + 3) * ⌊L' / ((1 - ε) * δ)⌋₊ + m' + n
        ≤ (n + 3) * ⌊L / ((1 - ε) * δ)⌋₊ + m
      ∧ Ld + surgeryPotential ε δ n L' m' ≤ surgeryPotential ε δ n L m := by sorry
