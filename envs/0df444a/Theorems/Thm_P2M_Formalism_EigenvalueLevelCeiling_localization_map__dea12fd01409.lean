-- Prove2me | Theorems.Thm_P2M_Formalism_EigenvalueLevelCeiling_localization_map__dea12fd01409
-- name    : P2M_Formalism_EigenvalueLevelCeiling_localization_map__dea12fd01409
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:55:04.048394+00:00
-- url     : https://prove2.me/theorems/49812026-fd66-4ff8-8af2-c4b571501e8f
-- title:
--   P2 M Formalism Eigenvalue Level Ceiling localization map  dea12fd01409: P2 M Formalism Eigenvalue Level Ceiling localization map  dea12fd01409
-- statement:
--   The P2 M Formalism Eigenvalue Level Ceiling localization map  dea12fd01409 construction uses the P2 M Formalism Eigenvalue Level Ceiling localization map  dea12fd01409 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/IdxRules.lean#L86-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/IdxRules.lean#L86-L99

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxRules
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped nonZeroDivisors
noncomputable section
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues Formalism.HermitianLatticesTheory
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] {V : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  {V' : Type*} [AddCommGroup V'] [Module K V'] [Module R V'] [IsScalarTower R K V']

theorem P2M_Formalism_EigenvalueLevelCeiling_localization_map__dea12fd01409 (p : Ideal R) [p.IsPrime] (φ : V →ₗ[K] V') (A : Submodule R V) :
    localization₂ p (A.map (φ.restrictScalars R)) = (localization₂ p A).map (φ.restrictScalars R) := by sorry

alias «Formalism».«EigenvalueLevelCeiling».«localization_map₄» := P2M_Formalism_EigenvalueLevelCeiling_localization_map__dea12fd01409
