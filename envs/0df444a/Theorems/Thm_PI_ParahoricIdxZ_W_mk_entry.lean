-- Prove2me | Theorems.Thm_PI_ParahoricIdxZ_W_mk_entry
-- name    : PI.ParahoricIdxZ.W.mk_entry
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:36:03.956261+00:00
-- url     : https://prove2.me/theorems/a166fd1c-563a-4d3b-bc7d-6a047ea0601d
-- title:
--   W: mk entry
-- statement:
--   The W construction uses the mk entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ParahoricIndexCount/CardRangeRedJ.lean#L52-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ParahoricIndexCount/CardRangeRedJ.lean#L52-L59

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_ThetaInjective
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_CardRangeRedJ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures.P.GLRed
open PI PI.ParahoricIdxZ PI.ParahoricIdxZ.W
variable {F : Type} [Field F] (O : Subring F) (ϖ : F) (hϖ : ϖ ∈ O)

theorem PI.ParahoricIdxZ.W.mk_entry {a t : ℕ} (g : Formalism.DoubleCosetMeasures.GLint O (a + t)) {A : Matrix (Fin a) (Fin a) F}
    {B : Matrix (Fin a) (Fin t) F} {C : Matrix (Fin t) (Fin a) F} {D : Matrix (Fin t) (Fin t) F}
    (hg : ((g : GL (Fin (a + t)) F) : Matrix _ _ F) = theta A B C D) (x y : Fin a ⊕ Fin t)
    (hv : Matrix.fromBlocks A B C D x y ∈ O) :
    Ideal.Quotient.mk (Ideal.span {(⟨ϖ, hϖ⟩ : O)}) (⟨((g : GL (Fin (a + t)) F) : Matrix _ _ F)
      (finSumFinEquiv x) (finSumFinEquiv y), g.2.1 _ _⟩ : O) =
      Ideal.Quotient.mk (Ideal.span {(⟨ϖ, hϖ⟩ : O)}) (⟨Matrix.fromBlocks A B C D x y, hv⟩ : O) := by sorry
