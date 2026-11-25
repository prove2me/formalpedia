-- Prove2me | Theorems.Thm_PI_ParahoricIdxZ_W_image_eq
-- name    : PI.ParahoricIdxZ.W.image_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:36:13.823818+00:00
-- url     : https://prove2.me/theorems/238ddd28-b15d-4c7f-aa62-1f1a196e7797
-- title:
--   W: image eq
-- statement:
--   The W construction uses the image eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ParahoricIndexCount/ParamInjective.lean#L30-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ParahoricIndexCount/ParamInjective.lean#L30-L119

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_CardRangeRedJ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_ParamInjective
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
variable {F : Type} [Field F] (O : Subring F) {ϖ : F} (hϖ : ϖ ∈ O)

theorem PI.ParahoricIdxZ.W.image_eq (hϖ0 : ϖ ≠ 0) (hloc : Formalism.DoubleCosetMeasures.IsLocalAt O ϖ) {a t : ℕ}
    (J' : Subgroup (GL (Fin a) F)) (hJint : J' ≤ Formalism.DoubleCosetMeasures.GLint O a)
    (J : Subgroup (GL (Fin (a + t)) F)) (hJ : ∀ A, A ∈ J ↔ blockCond O ϖ J' A) :
    (fun g : GL (Fin (a + t)) (Formalism.DoubleCosetMeasures.kF O ϖ hϖ) =>
      (g : Matrix (Fin (a + t)) (Fin (a + t)) (Formalism.DoubleCosetMeasures.kF O ϖ hϖ))) ''
      (((J.subgroupOf (Formalism.DoubleCosetMeasures.GLint O (a + t))).map (red O (a + t) ϖ hϖ) : Subgroup _) : Set _) =
      Set.range (param O hϖ J' hJint) := by sorry
