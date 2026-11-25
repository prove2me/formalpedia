-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_ampleRing_twist_subset_4861de94ddb8
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_ampleRing_twist_subset_4861de94ddb8
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T07:56:16.787809+00:00
-- url     : https://prove2.me/theorems/934bf75d-6666-4fdf-8760-0ca1c6b3bc71
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Graph Closed Alt ample Ring twist subset 4861de94ddb8: P2 M Ground Theory Heights  Heights Kleiman Graph Closed Alt ample Ring twist subset 4861de94ddb8
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Graph Closed Alt ample Ring twist subset 4861de94ddb8 construction uses the P2 M Ground Theory Heights  Heights Kleiman Graph Closed Alt ample Ring twist subset 4861de94ddb8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PGraphClosed.lean#L101-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PGraphClosed.lean#L101-L200

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_ampleRing_twist_subset_4861de94ddb8 (G H : SubSystem S x Ω) {r₁ r₂ : ℕ} (g : Fin (r₁ + 1) → Ω)
    (h : Fin (r₂ + 1) → Ω)
    (hgI : ∀ I, Submodule.span (chartRing S x I) (Set.range g) = G.sub I) (hh : IsVeryAmpleBy H h)
    {b₀ : Fin (r₁ + 1)} {l₀ : Fin (r₂ + 1)} (hne : h l₀ * g b₀ ≠ 0) (T : Subalgebra S Ω)
    (hT : ∀ b m, h m * g b / (h l₀ * g b₀) ∈ T) :
    ampleRing (G.twist H) 1 (h l₀ * g b₀) ⊆ T := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«GraphClosedAlt».«ampleRing_twist_subset» := P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_ampleRing_twist_subset_4861de94ddb8
