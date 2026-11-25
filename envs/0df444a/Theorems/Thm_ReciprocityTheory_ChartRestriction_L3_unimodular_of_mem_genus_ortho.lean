-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_unimodular_of_mem_genus_ortho
-- name    : ReciprocityTheory.ChartRestriction.L3.unimodular_of_mem_genus_ortho
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T14:28:06.73184+00:00
-- url     : https://prove2.me/theorems/426d6962-325a-4478-a502-f292d94d1dd7
-- title:
--   L3: unimodular of mem genus ortho
-- statement:
--   The L3 construction uses the unimodular of mem genus ortho property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/HermitianGenusExtension/SemilocalHermitianLattices/UnimodularOfMemGenusOrtho.lean#L35-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/HermitianGenusExtension/SemilocalHermitianLattices/UnimodularOfMemGenusOrtho.lean#L35-L43

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

theorem ReciprocityTheory.ChartRestriction.L3.unimodular_of_mem_genus_ortho (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) {I : Submodule (𝓞 K) V} {n : ℕ} (hI : Formalism.HermitianLatticesTheory.IsOrthoLattice h I n)
    {L : Submodule (𝓞 K) V} (hL : L ∈ Formalism.HermitianLatticesTheory.genus h I) :
    Submodule.IsLattice K L ∧ ∀ p : Ideal (𝓞 K), p.IsMaximal → Formalism.HermitianLatticesTheory.IsUnimodularAt h p L := by sorry
