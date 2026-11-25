-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_RationalUnipotent_unipElem_inv_smul_c1eaf2eb5e18
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_RationalUnipotent_unipElem_inv_smul_c1eaf2eb5e18
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:55:45.064566+00:00
-- url     : https://prove2.me/theorems/148596c1-686a-443d-908a-450fadee35b4
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Rational Unipotent unip Elem inv smul c1eaf2eb5e18: P2 M Ground Theory Heights  Heights Finite Covolume Rational Unipotent unip Elem inv smul c1eaf2
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Rational Unipotent unip Elem inv smul c1eaf2eb5e18 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Rational Unipotent unip Elem inv smul c1eaf2eb5e18 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PRationalUnipotent.lean#L81-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PRationalUnipotent.lean#L81-L84

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StRationalUnipotent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PRationalUnipotent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic
open scoped Pointwise
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]
open GroundTheory.Heights₂.Heights.FiniteCovolume.RationalUnipotent

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_RationalUnipotent_unipElem_inv_smul_c1eaf2eb5e18 (h : HermitianForm F E W) {x₀ y : W} {c : E}
    (hx₀ : h.toSesq x₀ x₀ = 0) (hy : h.toSesq x₀ y = 0)
    (hc : c + conj F E c = -h.toSesq y y) (x : W) :
    (unipElem h hx₀ hy hc)⁻¹ • x = unipMap h x₀ (-y) (conj F E c) x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«RationalUnipotent».«unipElem_inv_smul» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_RationalUnipotent_unipElem_inv_smul_c1eaf2eb5e18
