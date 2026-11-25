-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_exists_fin_generators_41e46a1db7ba
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_exists_fin_generators_41e46a1db7ba
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T06:40:10.506596+00:00
-- url     : https://prove2.me/theorems/4b952a11-e7de-5e74-a60c-093629687cc8
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Graph Closed Alt exists fin generators 41e46a1db7ba: P2 M Ground Theory Heights  Heights Kleiman Graph Closed Alt exists fin generators 41e46a1db7ba
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Graph Closed Alt exists fin generators 41e46a1db7ba construction uses the P2 M Ground Theory Heights  Heights Kleiman Graph Closed Alt exists fin generators 41e46a1db7ba property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PGraphClosed.lean#L24-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PGraphClosed.lean#L24-L79

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PGraphClosedLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PGraphClosed
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
open scoped Pointwise
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.GraphClosedAlt
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_exists_fin_generators_41e46a1db7ba (G : LineBundle S x) (hG : G.toSubSystem.Generated) :
    ∃ (r : ℕ) (g : Fin (r + 1) → Ω), (∀ a, g a ∈ G.toSubSystem.secs) ∧
      ∀ I, Submodule.span (chartRing S x I) (Set.range g) = G.sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«GraphClosedAlt».«exists_fin_generators» := P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_exists_fin_generators_41e46a1db7ba
