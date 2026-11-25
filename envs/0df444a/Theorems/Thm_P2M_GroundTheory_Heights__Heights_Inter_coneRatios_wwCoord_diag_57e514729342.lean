-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_coneRatios_wwCoord_diag_57e514729342
-- name    : P2M_GroundTheory_Heights__Heights_Inter_coneRatios_wwCoord_diag_57e514729342
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:34:18.607331+00:00
-- url     : https://prove2.me/theorems/46b2f2ca-1354-5305-a9b3-2fa74fa52220
-- title:
--   P2 M Ground Theory Heights  Heights Inter cone Ratios ww Coord diag 57e514729342: P2 M Ground Theory Heights  Heights Inter cone Ratios ww Coord diag 57e514729342
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter cone Ratios ww Coord diag 57e514729342 construction uses the P2 M Ground Theory Heights  Heights Inter cone Ratios ww Coord diag 57e514729342 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagRatioBasis.lean#L17-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagRatioBasis.lean#L17-L33

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StDiagRatioBasis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagRatioBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Inter_coneRatios_wwCoord_diag_57e514729342 {Ω : Type} [Field Ω] {ι ν κ : Type} {E : Type} [AddCommGroup E] [Module Ω E]
    {Φ : Type} [Field Φ] [Algebra Ω Φ] (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E)
    (φ : κ → E →ₗ[Ω] Ω) (a : Φ) (c : ∀ k, T.yyIdx ι ν κ k) :
    coneRatios (T.wwCoord x δ e φ a a) (diagChart c) = coneRatios (T.yyCoord x δ e φ a) c := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«coneRatios_wwCoord_diag» := P2M_GroundTheory_Heights__Heights_Inter_coneRatios_wwCoord_diag_57e514729342
