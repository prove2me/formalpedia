-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_isUnimodularAt_of_ortho
-- name    : ReciprocityTheory.ChartRestriction.L3.isUnimodularAt_of_ortho
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:57:01.990802+00:00
-- url     : https://prove2.me/theorems/d11b4539-f6e1-574a-b024-4c75aa555717
-- title:
--   L3: is Unimodular At of ortho
-- statement:
--   The L3 construction uses the is Unimodular At of ortho property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/HermitianGenusExtension/SemilocalHermitianLattices/FiniteDimensionalOfOrtho.lean#L164-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/HermitianGenusExtension/SemilocalHermitianLattices/FiniteDimensionalOfOrtho.lean#L164-L168

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
open StandardSymmetricSums

theorem ReciprocityTheory.ChartRestriction.L3.isUnimodularAt_of_ortho (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) {L : Submodule (𝓞 K) V} {n : ℕ} (hL : Formalism.HermitianLatticesTheory.IsOrthoLattice h L n) :
    ∀ p : Ideal (𝓞 K), p.IsMaximal → Formalism.HermitianLatticesTheory.IsUnimodularAt h p L := by sorry
