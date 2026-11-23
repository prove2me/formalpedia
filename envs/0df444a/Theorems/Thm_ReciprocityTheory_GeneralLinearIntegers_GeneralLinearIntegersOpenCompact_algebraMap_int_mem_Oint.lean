-- Prove2me | Theorems.Thm_ReciprocityTheory_GeneralLinearIntegers_GeneralLinearIntegersOpenCompact_algebraMap_int_mem_Oint
-- name    : ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.algebraMap_int_mem_Oint
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:20:12.838178+00:00
-- url     : https://prove2.me/theorems/b715019d-7c80-40fa-9885-3269ea37d4f8
-- title:
--   General Linear Integers Open Compact: algebra Map int mem Oint
-- statement:
--   The General Linear Integers Open Compact construction uses the algebra Map int mem Oint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeneralLinearIntegers/AlgebraMapIntMemOint.lean#L29-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeneralLinearIntegers/AlgebraMapIntMemOint.lean#L29-L32

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_AdeleLC
import Definitions.Def_ReciprocityTheory_GeneralLinearIntegers_AlgebraMapIntMemOint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.GeneralLinearIntegers ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped RestrictedProduct
variable {F : Type} [Field F] [NumberField F]

theorem ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.algebraMap_int_mem_Oint (m : 𝓞 F) :
    algebraMap F (FiniteAdeleRing (𝓞 F) F) (m : F) ∈ Oint F := by sorry
