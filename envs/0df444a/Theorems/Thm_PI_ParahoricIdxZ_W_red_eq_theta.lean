-- Prove2me | Theorems.Thm_PI_ParahoricIdxZ_W_red_eq_theta
-- name    : PI.ParahoricIdxZ.W.red_eq_theta
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:35:53.066079+00:00
-- url     : https://prove2.me/theorems/c312f539-05b0-5640-a9e3-a84280261017
-- title:
--   W: red eq theta
-- statement:
--   The W construction uses the red eq theta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ParahoricIndexCount/CardRangeRedJ.lean#L40-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ParahoricIndexCount/CardRangeRedJ.lean#L40-L50

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

theorem PI.ParahoricIdxZ.W.red_eq_theta {a t : ℕ} (h : Formalism.DoubleCosetMeasures.GLint O (a + t))
    (A : Matrix (Fin a) (Fin a) (Formalism.DoubleCosetMeasures.kF O ϖ hϖ)) (B : Matrix (Fin a) (Fin t) (Formalism.DoubleCosetMeasures.kF O ϖ hϖ))
    (C : Matrix (Fin t) (Fin a) (Formalism.DoubleCosetMeasures.kF O ϖ hϖ)) (D : Matrix (Fin t) (Fin t) (Formalism.DoubleCosetMeasures.kF O ϖ hϖ))
    (H : ∀ x y, Ideal.Quotient.mk _ (⟨((h : GL (Fin (a + t)) F) : Matrix _ _ F)
      (finSumFinEquiv x) (finSumFinEquiv y), h.2.1 _ _⟩ : O) = Matrix.fromBlocks A B C D x y) :
    ((red O (a + t) ϖ hϖ h : GL (Fin (a + t)) _) : Matrix _ _ _) = theta A B C D := by sorry
