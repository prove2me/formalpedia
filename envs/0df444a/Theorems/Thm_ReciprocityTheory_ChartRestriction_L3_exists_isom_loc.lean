-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_exists_isom_loc
-- name    : ReciprocityTheory.ChartRestriction.L3.exists_isom_loc
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:05:56.937395+00:00
-- url     : https://prove2.me/theorems/53edac33-d1b8-4063-b447-a3253be0f25e
-- title:
--   L3: exists isom loc
-- statement:
--   The L3 construction uses the exists isom loc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/HermitianGenusExtension/SemilocalHermitianLattices/ExistsIsomLoc.lean#L12-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/HermitianGenusExtension/SemilocalHermitianLattices/ExistsIsomLoc.lean#L12-L28

import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_GmapLocEqOfFrame
import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_ExistsIsomLoc
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

theorem ReciprocityTheory.ChartRestriction.L3.exists_isom_loc (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    {I : Submodule (𝓞 K) V} {n : ℕ} (hI : Formalism.HermitianLatticesTheory.IsOrthoLattice h I n)
    {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L) (p : Ideal (𝓞 K)) (hp : p.IsMaximal)
    (hu : Formalism.HermitianLatticesTheory.IsUnimodularAt h p L) :
    ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap g (Formalism.HermitianLatticesTheory.loc (K := K) p I) = Formalism.HermitianLatticesTheory.loc (K := K) p L := by sorry
