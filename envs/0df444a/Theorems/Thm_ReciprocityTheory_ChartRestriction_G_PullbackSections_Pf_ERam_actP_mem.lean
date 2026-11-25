-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_ERam_actP_mem
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam.actP_mem
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:37:45.846258+00:00
-- url     : https://prove2.me/theorems/a4b02ffe-5967-4d94-b1c0-f349703111df
-- title:
--   ERam: act P mem
-- statement:
--   The ERam construction uses the act P mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/EigRamLift.lean#L26-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/EigRamLift.lean#L26-L46

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_EigRamCore
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_GermSC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_EigRamLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [Field k] [Algebra ℚ k] [Algebra R k]

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam.actP_mem (hRQ : IsRQ (R := R) k) (B : FB R d O) (h : PS k 2 d) (hc : B.IsCanonGauge k h) {n : ℕ}
    (b : Fin n → O) (a : Fin n → R) {ξ : (Fin d → k) × (Fin d → k)} (hξ : ξ ∈ Hset (R := R) k h) :
    actP B b (fun i => algebraMap R k (a i)) ξ ∈ Hset (R := R) k h := by sorry
