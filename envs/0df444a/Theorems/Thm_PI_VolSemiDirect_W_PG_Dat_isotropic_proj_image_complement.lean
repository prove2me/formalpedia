-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_isotropic_proj_image_complement
-- name    : PI.VolSemiDirect.W.PG.Dat.isotropic_proj_image_complement
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:36:36.618365+00:00
-- url     : https://prove2.me/theorems/d41031df-7823-4ac8-abd2-289d245cb177
-- title:
--   Dat: isotropic proj image complement
-- statement:
--   The Dat construction uses the isotropic proj image complement property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/HermitianIsotropicProjComplement.lean#L58-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/HermitianIsotropicProjComplement.lean#L58-L61

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_HermitianIsotropicProjComplement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W PI.VolSemiDirect.W.PG
open Formalism.UG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
open PI.VolSemiDirect.W.PG.Dat
variable {D : Dat A n r}

theorem PI.VolSemiDirect.W.PG.Dat.isotropic_proj_image_complement {S : (n → A) →ₗ[A] (n → A)} (hS : D.FixEZ S) (hU : D.Uni S) {w : n → A}
    (hw : IsW D w) : D.pU (S w) = D.pX (S w) := by sorry
