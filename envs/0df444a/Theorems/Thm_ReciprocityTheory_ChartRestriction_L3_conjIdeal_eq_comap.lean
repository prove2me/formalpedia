-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_conjIdeal_eq_comap
-- name    : ReciprocityTheory.ChartRestriction.L3.conjIdeal_eq_comap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:19:30.313565+00:00
-- url     : https://prove2.me/theorems/7fc3aa73-acfc-459f-9579-b071b02eca2b
-- title:
--   L3: conj Ideal eq comap
-- statement:
--   The L3 construction uses the conj Ideal eq comap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/HermitianGenusExtension/SemilocalHermitianLattices/ExistsSqAbsNormOfInert.lean#L20-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/HermitianGenusExtension/SemilocalHermitianLattices/ExistsSqAbsNormOfInert.lean#L20-L37

import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_MassSt
import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_ExistsSqAbsNormOfInert
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L3
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem ReciprocityTheory.ChartRestriction.L3.conjIdeal_eq_comap (P : Ideal (𝓞 K)) :
    Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P.comap (conjO K) := by sorry
