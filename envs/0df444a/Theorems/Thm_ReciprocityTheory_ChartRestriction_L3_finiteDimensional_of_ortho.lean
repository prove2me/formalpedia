-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_finiteDimensional_of_ortho
-- name    : ReciprocityTheory.ChartRestriction.L3.finiteDimensional_of_ortho
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:47:56.680968+00:00
-- url     : https://prove2.me/theorems/3538f2cb-994b-5913-ac75-b89ced70db59
-- title:
--   L3: finite Dimensional of ortho
-- statement:
--   The L3 construction uses the finite Dimensional of ortho property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/HermitianGenusExtension/SemilocalHermitianLattices/FiniteDimensionalOfOrtho.lean#L79-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/HermitianGenusExtension/SemilocalHermitianLattices/FiniteDimensionalOfOrtho.lean#L79-L82

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

theorem ReciprocityTheory.ChartRestriction.L3.finiteDimensional_of_ortho {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V} {n : ℕ}
    (hL : Formalism.HermitianLatticesTheory.IsOrthoLattice h L n) : FiniteDimensional K V := by sorry
