-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LatticeLemmas_LocalChangeEq_spaceOf_inner_ccbadeb1b04f
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LatticeLemmas_LocalChangeEq_spaceOf_inner_ccbadeb1b04f
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:52:01.155955+00:00
-- url     : https://prove2.me/theorems/10f6afec-812e-4400-8f19-320319eee642
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Lattice Lemmas Local Change Eq space Of inner ccbadeb1b04f: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Lattic
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Lattice Lemmas Local Change Eq space Of inner ccbadeb1b04f construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Lattice Lemmas Local Change Eq space Of inner ccbadeb1b04f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/LocalChangeOfVectorSpace.lean#L113-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/LocalChangeOfVectorSpace.lean#L113-L121

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PLocalChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_LatticeOfLocalisationsHyps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_LocalChangeOfVectorSpace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LatticeLemmas
open NumberField NumberField.ComplexEmbedding TensorProduct IsDedekindDomain
  GroundTheory.Heights₂.Heights.ComplexAt
universe u v
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LatticeLemmas.LocalChangeEq
variable {K : Type*} [Field K] [NumberField K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {r : ℕ} (φ : V ≃ₗ[K] (Fin r → K))

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LatticeLemmas_LocalChangeEq_spaceOf_inner_ccbadeb1b04f (Nm : HermitianNorms K V) (σ : K →+* ℂ) (x y : V) :
    (Nm.form σ).inner ((1 : ComplexAt σ) ⊗ₜ x) (1 ⊗ₜ y) =
      ((spaceOf φ Nm).form σ).inner (coordMap r σ ((1 : ComplexAt σ) ⊗ₜ φ x))
        (coordMap r σ (1 ⊗ₜ φ y)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«LatticeLemmas».«LocalChangeEq».«spaceOf_inner» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LatticeLemmas_LocalChangeEq_spaceOf_inner_ccbadeb1b04f
