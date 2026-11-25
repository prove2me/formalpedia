-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_unipotent_proj_fixes_normal
-- name    : PI.LevelKSplit.W.SemiG.Dat.unipotent_proj_fixes_normal
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:37:43.537258+00:00
-- url     : https://prove2.me/theorems/2ec881a7-3206-5b6e-95a6-93537d41a0e9
-- title:
--   Dat: unipotent proj fixes normal
-- statement:
--   The Dat construction uses the unipotent proj fixes normal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/HermitianIsotropicProjComplement.lean#L102-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/HermitianIsotropicProjComplement.lean#L102-L103

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

theorem PI.LevelKSplit.W.SemiG.Dat.unipotent_proj_fixes_normal (H : D.Hyp) (S : (n → A) →ₗ[A] (n → A)) : D.Pi S D.z = D.z := by sorry
