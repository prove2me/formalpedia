-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_GtBCPf_trans_pull
-- name    : ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.trans_pull
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:32:38.40092+00:00
-- url     : https://prove2.me/theorems/98da228f-95e5-5d01-913a-816d48e6489f
-- title:
--   Gt BCPf: trans pull
-- statement:
--   The Gt BCPf construction uses the trans pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/BaseChangeKernels/TransPull.lean#L44-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/BaseChangeKernels/TransPull.lean#L44-L69

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_SiegelPullbackTransfer_ExistsGenTransfer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_TransPull
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
open Semi Geo.Tor

theorem ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.trans_pull {G' G B' B : Scheme.{0}} (a : G' ⟶ G) (q : G ⟶ B) (q' : G' ⟶ B') (F : B' ⟶ B)
    (hqb : q' ≫ F = a ≫ q) (L : LB B) (i i' : L.ι) {U U' : B.Opens} (hU : U ≤ L.U i)
    (hU' : U' ≤ L.U i') {V V' : B'.Opens} (hVi : V ≤ (L.pull F).U (pidx L F i))
    (hVi' : V' ≤ (L.pull F).U (pidx L F i'))
    (u : Γ(G, q ⁻¹ᵁ U)ˣ) (u' : Γ(G, q ⁻¹ᵁ U')ˣ)
    (h : res (q.preimage_mono (inf_le_right : U ⊓ U' ≤ U')) u' =
      pullU q _ (res (le_inf (inf_le_left.trans hU) (inf_le_right.trans hU')) (L.g i i')) *
        res (q.preimage_mono (inf_le_left : U ⊓ U' ≤ U)) u)
    (p : q' ⁻¹ᵁ V ≤ a ⁻¹ᵁ (q ⁻¹ᵁ U)) (p' : q' ⁻¹ᵁ V' ≤ a ⁻¹ᵁ (q ⁻¹ᵁ U')) :
    res (q'.preimage_mono (inf_le_right : V ⊓ V' ≤ V')) (res p' (pullU a _ u')) =
      pullU q' _ (res (le_inf (inf_le_left.trans hVi) (inf_le_right.trans hVi'))
        ((L.pull F).g (pidx L F i) (pidx L F i'))) *
        res (q'.preimage_mono (inf_le_left : V ⊓ V' ≤ V)) (res p (pullU a _ u)) := by sorry
