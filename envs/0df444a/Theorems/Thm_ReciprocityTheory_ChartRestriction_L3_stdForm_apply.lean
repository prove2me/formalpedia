-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_stdForm_apply
-- name    : ReciprocityTheory.ChartRestriction.L3.stdForm_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:20:12.68181+00:00
-- url     : https://prove2.me/theorems/c9dc4d83-7204-43eb-89a6-9b8623c34286
-- title:
--   L3: std Form apply
-- statement:
--   The L3 construction uses the std Form apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/HermitianGenusExtension/SemilocalHermitianLattices/FiniteDimensionalOfOrtho.lean#L22-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/HermitianGenusExtension/SemilocalHermitianLattices/FiniteDimensionalOfOrtho.lean#L22-L23

import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_MassSt
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_FiniteDimensionalOfOrtho
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

theorem ReciprocityTheory.ChartRestriction.L3.stdForm_apply (K : Type) [Field K] [StarRing K] (n : ℕ) (x y : Fin n → K) :
    stdForm K n x y = ∑ i, star (x i) * y i := by sorry
