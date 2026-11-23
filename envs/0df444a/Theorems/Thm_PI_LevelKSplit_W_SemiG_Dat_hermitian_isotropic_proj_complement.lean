-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_hermitian_isotropic_proj_complement
-- name    : PI.LevelKSplit.W.SemiG.Dat.hermitian_isotropic_proj_complement
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:33:39.410796+00:00
-- url     : https://prove2.me/theorems/3e236179-a4d4-4b11-8880-cbb15e3a5e29
-- title:
--   Dat: hermitian isotropic proj complement
-- statement:
--   The Dat construction uses the hermitian isotropic proj complement property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/HermitianIsotropicProjComplement.lean#L105-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/HermitianIsotropicProjComplement.lean#L105-L108

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

theorem PI.LevelKSplit.W.SemiG.Dat.hermitian_isotropic_proj_complement (H : D.Hyp) {w : n → A} (hw : IsW D w) (x : n → A) : D.h (D.pU x) w = 0 := by sorry
