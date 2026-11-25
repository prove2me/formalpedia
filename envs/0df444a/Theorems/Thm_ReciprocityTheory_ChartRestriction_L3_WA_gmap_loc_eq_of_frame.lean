-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_gmap_loc_eq_of_frame
-- name    : ReciprocityTheory.ChartRestriction.L3.WA.gmap_loc_eq_of_frame
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:47:51.390817+00:00
-- url     : https://prove2.me/theorems/df21e6d5-9dbf-5810-ba6f-786f391682c0
-- title:
--   WA: gmap loc eq of frame
-- statement:
--   The WA construction uses the gmap loc eq of frame property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/HermitianGenusExtension/SemilocalHermitianLattices/GmapLocEqOfFrame.lean#L79-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/HermitianGenusExtension/SemilocalHermitianLattices/GmapLocEqOfFrame.lean#L79-L122

import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_ExistsIsomFrame
import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_IsHermSemilocalLocRing
import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_UnimodularOfMemGenusOrtho
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_TraceReal
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_GmapLocEqOfFrame
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem ReciprocityTheory.ChartRestriction.L3.WA.gmap_loc_eq_of_frame {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    {p : Ideal (𝓞 K)} (hp : p.IsPrime) (hu : Formalism.HermitianLatticesTheory.IsUnimodularAt h p L) {n : ℕ} {e : Fin n → V}
    (hspan : Submodule.span K (Set.range e) = ⊤)
    (he : ∀ i j, h (e i) (e j) = if i = j then 1 else 0) {g : V ≃ₗ[K] V}
    (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) (hge : ∀ i, g (e i) ∈ Formalism.HermitianLatticesTheory.loc (K := K) p L) :
    Formalism.HermitianLatticesTheory.gmap g (Formalism.HermitianLatticesTheory.loc (K := K) p (Submodule.span (𝓞 K) (Set.range e))) =
      Formalism.HermitianLatticesTheory.loc (K := K) p L := by sorry
