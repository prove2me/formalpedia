-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_complement_proj_image
-- name    : PI.LevelKSplit.W.SemiG.Dat.complement_proj_image
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T00:21:25.739081+00:00
-- url     : https://prove2.me/theorems/25f884f9-73c4-44c1-9a57-1bf1e1d91f8b
-- title:
--   Dat: complement proj image
-- statement:
--   The Dat construction uses the complement proj image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/HermitianIsotropicProjComplement.lean#L84-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/HermitianIsotropicProjComplement.lean#L84-L87

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

theorem PI.LevelKSplit.W.SemiG.Dat.complement_proj_image {S : (n → A) →ₗ[A] (n → A)} (hW : D.MapW S) {w : n → A} (hw : IsW D w) :
    D.pW (S w) = S w - D.pX (S w) := by sorry
