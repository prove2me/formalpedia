-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Rs_ctstepglue_conj_block
-- name    : PositivityTheory.Rg.Rs.ctstepglue.conj_block
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:52:31.603576+00:00
-- url     : https://prove2.me/theorems/28dc85fa-ab98-4f01-88e6-e5bf1d1fc7a6
-- title:
--   ctstepglue: conj block
-- statement:
--   The ctstepglue construction uses the conj block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ResidualSpectrum/ExponentialNegativity/ConstantTermSteps/ConjBlock.lean#L7-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ResidualSpectrum/ExponentialNegativity/ConstantTermSteps/ConjBlock.lean#L7-L49

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_ExponentialNegativity_ConstantTermSteps_ConjBlock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.ctstepglue
open Matrix

theorem PositivityTheory.Rg.Rs.ctstepglue.conj_block {R : Type*} [CommRing R] {n : ℕ} (r : ℕ) (b : GL (Fin n) R)
    (hb : (b : Matrix (Fin n) (Fin n) R).BlockTriangular id) (d : Fin n → Rˣ)
    (hd : ∀ i j : Fin n, ((i : ℕ) < r ↔ (j : ℕ) < r) → d i = d j) :
    ∃ Y : Matrix (Fin n) (Fin n) R, (∀ i j : Fin n, ¬((i : ℕ) < r ∧ r ≤ (j : ℕ)) → Y i j = 0) ∧
      (b : Matrix (Fin n) (Fin n) R) * diagonal (fun i => (d i : R)) =
        (1 + Y) * (diagonal (fun i => (d i : R)) * (b : Matrix (Fin n) (Fin n) R)) := by sorry
