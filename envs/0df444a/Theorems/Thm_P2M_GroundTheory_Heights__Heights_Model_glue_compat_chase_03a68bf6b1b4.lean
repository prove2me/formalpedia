-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_glue_compat_chase_03a68bf6b1b4
-- name    : P2M_GroundTheory_Heights__Heights_Model_glue_compat_chase_03a68bf6b1b4
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:38:13.242991+00:00
-- url     : https://prove2.me/theorems/2022b3f8-4f6f-55dd-aa6d-def99c8deaed
-- title:
--   P2 M Ground Theory Heights  Heights Model glue compat chase 03a68bf6b1b4: P2 M Ground Theory Heights  Heights Model glue compat chase 03a68bf6b1b4
-- statement:
--   The P2 M Ground Theory Heights  Heights Model glue compat chase 03a68bf6b1b4 construction uses the P2 M Ground Theory Heights  Heights Model glue compat chase 03a68bf6b1b4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/GlueCoherence.lean#L126-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/GlueCoherence.lean#L126-L177

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_GlueCoherence
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory Limits AlgebraicGeometry
noncomputable section
set_option linter.unusedSimpArgs false
universe u
variable {T' T Y Z : Scheme.{u}}

theorem P2M_GroundTheory_Heights__Heights_Model_glue_compat_chase_03a68bf6b1b4 {X XQ Xp V U W Oa Oam ON : Scheme.{0}}
    {ιV : V ⟶ X} {ιU : U ⟶ X} {ιW : W ⟶ X} {jV : W ⟶ V} {jU : W ⟶ U}
    {bQ : XQ ⟶ X} {bp : Xp ⟶ X} {rQp : XQ ⟶ Xp} {c0 : XQ ⟶ V} {rU : Xp ⟶ U}
    {ρU : U ⟶ ON} {rN : Xp ⟶ ON} {ρa : Oa ⟶ ON} {τa : Oa ⟶ V} {cA : XQ ⟶ Oa}
    {h : Oam ⟶ Oa} {cA' : XQ ⟶ Oam} {t : W ⟶ Oam} {k : W ⟶ Oa} {q : XQ ⟶ W}
    (hV : jV ≫ ιV = ιW) (hU : jU ≫ ιU = ιW) (h0 : c0 ≫ ιV = bQ) (hp : rQp ≫ bp = bQ)
    (hrU : rU ≫ ιU = bp) (h5 : rU ≫ ρU = rN) (e1 : cA ≫ ρa = rQp ≫ rN) (e2 : cA ≫ τa = c0)
    (ee : cA' ≫ h = cA) (ek : t ≫ h = k) (e7 : k ≫ ρa = jU ≫ ρU) (e8 : k ≫ τa = jV)
    (qV : q ≫ jV = c0) (qU : q ≫ jU = rQp ≫ rU) (qt : q ≫ t = cA') (qW : q ≫ ιW = bQ)
    {E : X.Modules} {E₀ : V.Modules} {Ep : Xp.Modules} {E' : ON.Modules}
    (e₀ : (Scheme.Modules.pullback ιV).obj E ≅ E₀)
    (eU : (Scheme.Modules.pullback ιU).obj E ≅ (Scheme.Modules.pullback ρU).obj E')
    (σ : (Scheme.Modules.pullback rN).obj E' ≅ Ep)
    (β : (Scheme.Modules.pullback rQp).obj Ep ≅ (Scheme.Modules.pullback c0).obj E₀)
    (ψ : (Scheme.Modules.pullback h).obj ((Scheme.Modules.pullback ρa).obj E') ≅
      (Scheme.Modules.pullback h).obj ((Scheme.Modules.pullback τa).obj E₀))
    (hψ : pullbackIsoAlong ee ψ =
      (pullbackCompIso e1 (Iso.refl ((Scheme.Modules.pullback ρa).obj E'))).symm ≪≫
        pullbackCompIso (rfl : rQp ≫ rN = rQp ≫ rN) σ ≪≫ β ≪≫
        pullbackCompIso e2 (Iso.refl ((Scheme.Modules.pullback τa).obj E₀)))
    (hglue : pullbackCompIso hV e₀ = pullbackCompIso hU eU ≪≫ starIso ek e7 e8 ψ) :
    pullbackCompIso h0 e₀ =
      pullbackCompIso hp (pullbackCompIso hrU eU ≪≫
        ((pullbackCompIso h5 (Iso.refl ((Scheme.Modules.pullback ρU).obj E'))).symm ≪≫ σ)) ≪≫ β := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«glue_compat_chase» := P2M_GroundTheory_Heights__Heights_Model_glue_compat_chase_03a68bf6b1b4
