-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locEmb_mk_cfee296f451f
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_locEmb_mk_cfee296f451f
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:09:42.876062+00:00
-- url     : https://prove2.me/theorems/ed41c41d-5e77-40fc-ac06-bec72dc9bfd9
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman loc Emb mk cfee296f451f: P2 M Ground Theory Heights  Heights Kleiman loc Emb mk cfee296f451f
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman loc Emb mk cfee296f451f construction uses the P2 M Ground Theory Heights  Heights Kleiman loc Emb mk cfee296f451f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistSplitLoc.lean#L97-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistSplitLoc.lean#L97-L106

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistSplitChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistSplitLoc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Pointwise AddMonoidAlgebra
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {r : ℕ} (η : Fin (r + 1) → Ω)
variable (M₀ : FinGradedSub (S := S) (x := x) Ω)

theorem P2M_GroundTheory_Heights__Heights_Kleiman_locEmb_mk_cfee296f451f {I : Finset (Fin (N + 1))} (hI : I ⊆ support x) (m : TwM η M₀)
    (s : monos (S := MvPolynomial (Fin (r + 1)) S) I) {e : ℕ} {v : Ω}
    (h : xyHom S x η s = single ((0 : ℤ), (e : ℤ)) v) (hv : v ≠ 0) :
    UT.toL (locEmb η M₀ I hI (LocalizedModule.mk m s)) = single ((0 : ℤ), -(e : ℤ)) v⁻¹ * m.val := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«locEmb_mk» := P2M_GroundTheory_Heights__Heights_Kleiman_locEmb_mk_cfee296f451f
