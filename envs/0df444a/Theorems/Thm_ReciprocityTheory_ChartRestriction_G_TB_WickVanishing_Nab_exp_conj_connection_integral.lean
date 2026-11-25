-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_exp_conj_connection_integral
-- name    : ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.exp_conj_connection_integral
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:42:47.805288+00:00
-- url     : https://prove2.me/theorems/e3dd2ce0-9418-5492-9972-b57723153ad8
-- title:
--   Nab: exp conj connection integral
-- statement:
--   The Nab construction uses the exp conj connection integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/ExpConjConnectionIntegral.lean#L40-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/ExpConjConnectionIntegral.lean#L40-L82

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SigCancel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ExpConjConnectionIntegral
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]

theorem ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.exp_conj_connection_integral {B : FB R d O} {h : PS k 2 d} (hc : B.IsCanonGauge k h) (w0 : O) (hw : w0 + star w0 = 1)
    (m : ℕ) (u' φ' : Fin d → R) (G : AA k d) (hG : G ∈ Ig R k (Fin d ⊕ Fin d)) :
    liftX k (FB.expS k (-((m : k) • B.hL k h w0))) *
      nabla k B h m (fun i => algebraMap R k (u' i))
        (fun i => algebraMap R k (φ' i) - (sg1 k h).mulVec (fun j => algebraMap R k (u' j)) i)
        (liftX k (FB.expS k ((m : k) • B.hL k h w0)) * G) ∈ Ig R k (Fin d ⊕ Fin d) := by sorry
