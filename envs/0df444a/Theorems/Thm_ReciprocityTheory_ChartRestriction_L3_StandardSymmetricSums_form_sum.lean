-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_StandardSymmetricSums_form_sum
-- name    : ReciprocityTheory.ChartRestriction.L3.StandardSymmetricSums.form_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:20:31.258579+00:00
-- url     : https://prove2.me/theorems/b4bd0bce-8a17-4ba5-8d7c-b959014f8a80
-- title:
--   Standard Symmetric Sums: form sum
-- statement:
--   The Standard Symmetric Sums construction uses the form sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/HermitianGenusExtension/SemilocalHermitianLattices/FiniteDimensionalOfOrtho.lean#L52-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/HermitianGenusExtension/SemilocalHermitianLattices/FiniteDimensionalOfOrtho.lean#L52-L55

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
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
open ReciprocityTheory.ChartRestriction.L3.StandardSymmetricSums

theorem ReciprocityTheory.ChartRestriction.L3.StandardSymmetricSums.form_sum {h : V →ₗ⋆[K] V →ₗ[K] K} {n : ℕ} {e : Fin n → V}
    (he : ∀ i j, h (e i) (e j) = if i = j then 1 else 0) (c d : Fin n → K) :
    h (∑ i, c i • e i) (∑ j, d j • e j) = ∑ i, star (c i) * d i := by sorry
