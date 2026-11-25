-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_comap_wwIdeal_yyEmb_f63c049915a6
-- name    : P2M_GroundTheory_Heights__Heights_Inter_comap_wwIdeal_yyEmb_f63c049915a6
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:33:59.044352+00:00
-- url     : https://prove2.me/theorems/147123fc-80f5-5630-9a94-bc98f2673005
-- title:
--   P2 M Ground Theory Heights  Heights Inter comap ww Ideal yy Emb f63c049915a6: P2 M Ground Theory Heights  Heights Inter comap ww Ideal yy Emb f63c049915a6
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter comap ww Ideal yy Emb f63c049915a6 construction uses the P2 M Ground Theory Heights  Heights Inter comap ww Ideal yy Emb f63c049915a6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFibreProduct.lean#L25-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFibreProduct.lean#L25-L34

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

theorem P2M_GroundTheory_Heights__Heights_Inter_comap_wwIdeal_yyEmb_f63c049915a6 {Ω : Type} [Field Ω] {ι ν κ : Type} {E : Type} [AddCommGroup E]
    [Module Ω E] {Φ : Type} [Field Φ] [Algebra Ω Φ] (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E)
    (φ : κ → E →ₗ[Ω] Ω) (a : Fin 2 → Φ) (j : Fin 2) :
    (T.wwIdeal x δ e φ (a 0) (a 1)).comap
        (rename (T.yyEmb j) : MRing (T.yyIdx ι ν κ) →ₐ[ℤ] MRing (T.wwIdx ι ν κ)).toRingHom =
      T.yyIdeal x δ e φ (a j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«comap_wwIdeal_yyEmb» := P2M_GroundTheory_Heights__Heights_Inter_comap_wwIdeal_yyEmb_f63c049915a6
