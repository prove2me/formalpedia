-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_FnDegAdjoin_quotEquiv_mk_e3a6de09a4c9
-- name    : P2M_GroundTheory_Heights__Heights_Inter_FnDegAdjoin_quotEquiv_mk_e3a6de09a4c9
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:23:18.548509+00:00
-- url     : https://prove2.me/theorems/1629163a-4d4c-4c33-ab6a-2cbdb97bba8c
-- title:
--   P2 M Ground Theory Heights  Heights Inter Fn Deg Adjoin quot Equiv mk e3a6de09a4c9: P2 M Ground Theory Heights  Heights Inter Fn Deg Adjoin quot Equiv mk e3a6de09a4c9
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Fn Deg Adjoin quot Equiv mk e3a6de09a4c9 construction uses the P2 M Ground Theory Heights  Heights Inter Fn Deg Adjoin quot Equiv mk e3a6de09a4c9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFnDegAdjoin.lean#L24-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFnDegAdjoin.lean#L24-L27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFnDegAdjoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChartRankAdjoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFnDegAdjoin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
open GroundTheory.Heights₂.Heights.Inter.FnDegAdjoin
variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] {σ : Type}

theorem P2M_GroundTheory_Heights__Heights_Inter_FnDegAdjoin_quotEquiv_mk_e3a6de09a4c9 (g : σ → Ω) (I : Ideal (MvPolynomial σ F))
    (h : I = RingHom.ker (aeval g : MvPolynomial σ F →ₐ[F] Ω)) (p : MvPolynomial σ F) :
    (quotEquiv g I h (Ideal.Quotient.mk I p) : Ω) = aeval g p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«FnDegAdjoin».«quotEquiv_mk» := P2M_GroundTheory_Heights__Heights_Inter_FnDegAdjoin_quotEquiv_mk_e3a6de09a4c9
