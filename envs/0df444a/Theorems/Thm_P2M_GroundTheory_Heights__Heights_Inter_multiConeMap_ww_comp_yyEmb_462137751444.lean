-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_multiConeMap_ww_comp_yyEmb_462137751444
-- name    : P2M_GroundTheory_Heights__Heights_Inter_multiConeMap_ww_comp_yyEmb_462137751444
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:24:46.56027+00:00
-- url     : https://prove2.me/theorems/5081cf6d-18ca-41a1-a7f8-12b83143bd9e
-- title:
--   P2 M Ground Theory Heights  Heights Inter multi Cone Map ww comp yy Emb 462137751444: P2 M Ground Theory Heights  Heights Inter multi Cone Map ww comp yy Emb 462137751444
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter multi Cone Map ww comp yy Emb 462137751444 construction uses the P2 M Ground Theory Heights  Heights Inter multi Cone Map ww comp yy Emb 462137751444 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFibreProduct.lean#L11-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFibreProduct.lean#L11-L23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsFibreProduct
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFibreProduct
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I4
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Inter_multiConeMap_ww_comp_yyEmb_462137751444 {Ω : Type} [Field Ω] {ι ν κ : Type} {E : Type} [AddCommGroup E]
    [Module Ω E] {Φ : Type} [Field Φ] [Algebra Ω Φ] (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E)
    (φ : κ → E →ₗ[Ω] Ω) (a : Fin 2 → Φ) (j : Fin 2) :
    (T.multiConeMap (T.wwCoord x δ e φ (a 0) (a 1))).comp
        (rename (T.yyEmb j) : MRing (T.yyIdx ι ν κ) →ₐ[ℤ] MRing (T.wwIdx ι ν κ)).toRingHom =
      (rename (diagonalBlockIndex j) : MvPolynomial T.YBlk Φ →ₐ[Φ] MvPolynomial T.WBlk Φ).toRingHom.comp
        (T.multiConeMap (T.yyCoord x δ e φ (a j))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«multiConeMap_ww_comp_yyEmb» := P2M_GroundTheory_Heights__Heights_Inter_multiConeMap_ww_comp_yyEmb_462137751444
