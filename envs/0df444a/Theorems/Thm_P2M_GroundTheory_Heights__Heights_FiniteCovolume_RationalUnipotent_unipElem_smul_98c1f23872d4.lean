-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_RationalUnipotent_unipElem_smul_98c1f23872d4
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_RationalUnipotent_unipElem_smul_98c1f23872d4
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:55:20.928037+00:00
-- url     : https://prove2.me/theorems/68b92bba-6948-4345-9b8c-7a602030e8f0
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Rational Unipotent unip Elem smul 98c1f23872d4: P2 M Ground Theory Heights  Heights Finite Covolume Rational Unipotent unip Elem smul 98c1f23872d4
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Rational Unipotent unip Elem smul 98c1f23872d4 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Rational Unipotent unip Elem smul 98c1f23872d4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PRationalUnipotent.lean#L76-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PRationalUnipotent.lean#L76-L79

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_RationalUnipotent_unipElem_smul_98c1f23872d4 (h : HermitianForm F E W) {x₀ y : W} {c : E}
    (hx₀ : h.toSesq x₀ x₀ = 0) (hy : h.toSesq x₀ y = 0)
    (hc : c + conj F E c = -h.toSesq y y) (x : W) :
    unipElem h hx₀ hy hc • x = unipMap h x₀ y c x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«RationalUnipotent».«unipElem_smul» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_RationalUnipotent_unipElem_smul_98c1f23872d4
