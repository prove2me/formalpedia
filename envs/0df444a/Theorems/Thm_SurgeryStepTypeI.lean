-- Prove2me | Theorems.Thm_SurgeryStepTypeI
-- name    : SurgeryStepTypeI
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:14:24.740522+00:00
-- url     : https://prove2.me/theorems/91f134d1-a400-439c-8c3a-96a47a79e5aa
-- title:
--   Surgery Step Type I: Surgery Step Type I
-- statement:
--   The amortization step for a Type I surgery cut (paper.tex 1005-1075, ``Algorithm 1'', Type I
--   branch), isolated as pure real/natural-number arithmetic. Given the numerical output of a Type I
--   cut at scale `β ≥ δ` -- the kept curve's length `L' ≥ 0` and small-edge count `m'`, the discarded
--   curve's length `Ld`, against the input length `L` and small-edge count `m`, subject to
--   `L' ≤ L - (1-ε)β`, `L' + Ld ≤ L + 2εβ` and `m' ≤ m + 3` -- both halves of the induction step
--   follow: the termination measure `M(L,m) = (n+3)⌊L/((1-ε)δ)⌋ + m` drops by at least `n` (the
--   floor term falls by at least one, paying the `+3` small-edge slack), and the potential
--   `surgeryPotential` pays for the discarded length.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/SurgeryStepTypeI.lean#L12-L57
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/SurgeryStepTypeI.lean#L12-L57

import Definitions.Def_Tablet_surgeryPotential
import Definitions.Def_Tablet_SurgeryStepTypeI
set_option autoImplicit false

theorem SurgeryStepTypeI (δ ε : ℝ) (n : ℕ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hδ : 0 < δ) (hn : 0 < n) (L L' Ld β : ℝ) (m m' : ℕ)
    (hL'0 : 0 ≤ L') (hbeta : δ ≤ β)
    (hlen : L' ≤ L - (1 - ε) * β) (htot : L' + Ld ≤ L + 2 * ε * β)
    (hm : m' ≤ m + 3) :
    (n + 3) * ⌊L' / ((1 - ε) * δ)⌋₊ + m' + n
        ≤ (n + 3) * ⌊L / ((1 - ε) * δ)⌋₊ + m
      ∧ Ld + surgeryPotential ε δ n L' m' ≤ surgeryPotential ε δ n L m := by sorry
