-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_isUnimodularAt_gmap
-- name    : ReciprocityTheory.ChartRestriction.L3.isUnimodularAt_gmap
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:48:55.74677+00:00
-- url     : https://prove2.me/theorems/dc68d7cf-d3a8-4ad1-8dba-1bb1b59642fa
-- title:
--   L3: is Unimodular At gmap
-- statement:
--   The L3 construction uses the is Unimodular At gmap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/HermitianGenusExtension/SemilocalHermitianLattices/UnimodularOfMemGenusOrtho.lean#L22-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/HermitianGenusExtension/SemilocalHermitianLattices/UnimodularOfMemGenusOrtho.lean#L22-L27

import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_FiniteDimensionalOfOrtho
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovolBound
import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_UnimodularOfMemGenusOrtho
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

theorem ReciprocityTheory.ChartRestriction.L3.isUnimodularAt_gmap {h : V →ₗ⋆[K] V →ₗ[K] K} {g : V ≃ₗ[K] V}
    (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) (p : Ideal (𝓞 K)) (L : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.IsUnimodularAt h p (Formalism.HermitianLatticesTheory.gmap g L) ↔ Formalism.HermitianLatticesTheory.IsUnimodularAt h p L := by sorry
