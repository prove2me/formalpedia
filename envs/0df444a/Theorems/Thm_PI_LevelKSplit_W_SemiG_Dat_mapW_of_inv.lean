-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_mapW_of_inv
-- name    : PI.LevelKSplit.W.SemiG.Dat.mapW_of_inv
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:35:25.186818+00:00
-- url     : https://prove2.me/theorems/9450af9e-e2de-4b18-be2e-cdffaedc79dd
-- title:
--   Dat: map W of inv
-- statement:
--   The Dat construction uses the map W of inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/HermitianIsotropicProjComplement.lean#L181-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/HermitianIsotropicProjComplement.lean#L181-L189

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

theorem PI.LevelKSplit.W.SemiG.Dat.mapW_of_inv {S Si : (n → A) →ₗ[A] (n → A)} (hSSi : ∀ v, S (Si v) = v) (hU : D.Uni S)
    (hXi : D.MapX Si) (hZi : Si D.z - D.z ∈ Submodule.span A (Set.range D.e)) : D.MapW S := by sorry
