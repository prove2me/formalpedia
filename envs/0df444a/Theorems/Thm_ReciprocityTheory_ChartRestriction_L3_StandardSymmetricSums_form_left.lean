-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_StandardSymmetricSums_form_left
-- name    : ReciprocityTheory.ChartRestriction.L3.StandardSymmetricSums.form_left
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:48:15.599544+00:00
-- url     : https://prove2.me/theorems/e989ad32-0041-51eb-a0dd-67126bb45ad4
-- title:
--   Standard Symmetric Sums: form left
-- statement:
--   The Standard Symmetric Sums construction uses the form left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/HermitianGenusExtension/SemilocalHermitianLattices/FiniteDimensionalOfOrtho.lean#L57-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/HermitianGenusExtension/SemilocalHermitianLattices/FiniteDimensionalOfOrtho.lean#L57-L60

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

theorem ReciprocityTheory.ChartRestriction.L3.StandardSymmetricSums.form_left {h : V →ₗ⋆[K] V →ₗ[K] K} {n : ℕ} {e : Fin n → V}
    (he : ∀ i j, h (e i) (e j) = if i = j then 1 else 0) (i : Fin n) (d : Fin n → K) :
    h (e i) (∑ j, d j • e j) = d i := by sorry
