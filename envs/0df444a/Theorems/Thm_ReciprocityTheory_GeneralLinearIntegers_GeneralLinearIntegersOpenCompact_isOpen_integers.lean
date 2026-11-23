-- Prove2me | Theorems.Thm_ReciprocityTheory_GeneralLinearIntegers_GeneralLinearIntegersOpenCompact_isOpen_integers
-- name    : ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isOpen_integers
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:57:22.161731+00:00
-- url     : https://prove2.me/theorems/8eee32f1-1cdb-4ffb-aac9-ff1edf03631b
-- title:
--   General Linear Integers Open Compact: is Open integers
-- statement:
--   The General Linear Integers Open Compact construction uses the is Open integers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeneralLinearIntegers/AlgebraMapIntMemOint.lean#L17-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeneralLinearIntegers/AlgebraMapIntMemOint.lean#L17-L21

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

theorem ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isOpen_integers (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by sorry
