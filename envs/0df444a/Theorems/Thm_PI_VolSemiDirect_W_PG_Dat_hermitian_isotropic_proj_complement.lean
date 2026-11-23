-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_hermitian_isotropic_proj_complement
-- name    : PI.VolSemiDirect.W.PG.Dat.hermitian_isotropic_proj_complement
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:48:48.771546+00:00
-- url     : https://prove2.me/theorems/cbeed2dd-eba3-4fe2-b0d3-642d7da54c69
-- title:
--   Dat: hermitian isotropic proj complement
-- statement:
--   The Dat construction uses the hermitian isotropic proj complement property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/HermitianIsotropicProjComplement.lean#L91-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/HermitianIsotropicProjComplement.lean#L91-L93

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

theorem PI.VolSemiDirect.W.PG.Dat.hermitian_isotropic_proj_complement (H : D.Hyp) {w : n → A} (hw : IsW D w) (x : n → A) : D.h (D.pU x) w = 0 := by sorry
