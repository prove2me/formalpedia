-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_lift_scalar_da883d6bb72e
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_lift_scalar_da883d6bb72e
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:03:53.939845+00:00
-- url     : https://prove2.me/theorems/3c7e495b-cd7b-5a1b-b78c-96aeb9578ace
-- title:
--   P2 M Formalism Basic Notions Examples  NZ lift scalar da883d6bb72e: P2 M Formalism Basic Notions Examples  NZ lift scalar da883d6bb72e
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ lift scalar da883d6bb72e construction uses the P2 M Formalism Basic Notions Examples  NZ lift scalar da883d6bb72e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeF.lean#L70-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeF.lean#L70-L76

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeE
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeC
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.NZ
open MonoidAlgebra
attribute [local instance] Classical.propDecidable
variable {K : Type} [Field K]
variable {I : Type} [Fintype I] {G : I → Type} [∀ i, Group (G i)] [∀ i, Finite (G i)]
variable {L : I → Type} [∀ i, Fintype (L i)] (E : ∀ i, L i → MonoidAlgebra K (G i)) (S : (∀ i, L i) → Prop)

theorem P2M_Formalism_BasicNotions_Examples__NZ_lift_scalar_da883d6bb72e {Γ V : Type} [Group Γ] [Finite Γ] [AddCommGroup V] [Module K V] (Ψ : Γ →* K)
    (F : Γ →* Module.End K V) (hF : ∀ g, F g = Ψ g • 1) (x : MonoidAlgebra K Γ) :
    MonoidAlgebra.lift K (Module.End K V) Γ F x = evS Ψ x • 1 := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«lift_scalar» := P2M_Formalism_BasicNotions_Examples__NZ_lift_scalar_da883d6bb72e
