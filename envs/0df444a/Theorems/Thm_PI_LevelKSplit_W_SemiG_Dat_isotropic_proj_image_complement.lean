-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_isotropic_proj_image_complement
-- name    : PI.LevelKSplit.W.SemiG.Dat.isotropic_proj_image_complement
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:35:19.969655+00:00
-- url     : https://prove2.me/theorems/01e166bc-0aff-47c5-98d6-e495840f5e5b
-- title:
--   Dat: isotropic proj image complement
-- statement:
--   The Dat construction uses the isotropic proj image complement property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/HermitianIsotropicProjComplement.lean#L78-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/HermitianIsotropicProjComplement.lean#L78-L82

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemiGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_HermitianIsotropicProjComplement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.SemiG
open Formalism.UG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
open PI.LevelKSplit.W.SemiG.Dat
variable {D : Dat A n r}

theorem PI.LevelKSplit.W.SemiG.Dat.isotropic_proj_image_complement {S : (n → A) →ₗ[A] (n → A)} (hW : D.MapW S) {w : n → A} (hw : IsW D w) :
    D.pU (S w) = D.pX (S w) := by sorry
