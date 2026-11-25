-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperSubquotientFinite_isNoetherianRing_chart_5008a51ed2a5
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SnapperSubquotientFinite_isNoetherianRing_chart_5008a51ed2a5
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:10:12.78833+00:00
-- url     : https://prove2.me/theorems/e5f6d381-fafb-5287-b487-e6d25b768642
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Snapper Subquotient Finite is Noetherian Ring chart 5008a51ed2a5: P2 M Ground Theory Heights  Heights Kleiman Snapper Subquotient Finite is Noetherian Ring
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Snapper Subquotient Finite is Noetherian Ring chart 5008a51ed2a5 construction uses the P2 M Ground Theory Heights  Heights Kleiman Snapper Subquotient Finite is Noetherian Ring chart 5008a51ed2a5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperSubquotFinite.lean#L67-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperSubquotFinite.lean#L67-L69

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperSubquotFiniteSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperQuotAdd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperSubquotFinite
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
open MvPolynomial
noncomputable section
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.SnapperSubquotientFinite
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SnapperSubquotientFinite_isNoetherianRing_chart_5008a51ed2a5 [IsNoetherianRing S] (I : Chart x) : IsNoetherianRing (chartRing S x I) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SnapperSubquotientFinite».«isNoetherianRing_chart» := P2M_GroundTheory_Heights__Heights_Kleiman_SnapperSubquotientFinite_isNoetherianRing_chart_5008a51ed2a5
