-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LatticeLemmas_LocalChangeEq_bAt_of_aAt_bd1074445082
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LatticeLemmas_LocalChangeEq_bAt_of_aAt_bd1074445082
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:44:17.623264+00:00
-- url     : https://prove2.me/theorems/b6bd2dd4-8aa4-592e-a7c5-e910c93964e0
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Lattice Lemmas Local Change Eq b At of a At bd1074445082: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Lattice
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Lattice Lemmas Local Change Eq b At of a At bd1074445082 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Lattice Lemmas Local Change Eq b At of a At bd1074445082 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/LocalChangeOfVectorSpace.lean#L252-L286
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/LocalChangeOfVectorSpace.lean#L252-L286

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
variable (v : HeightOneSpectrum (𝓞 K))
include φ

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LatticeLemmas_LocalChangeEq_bAt_of_aAt_bd1074445082 (hA : AAt K V) : BAt K r := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«LatticeLemmas».«LocalChangeEq».«bAt_of_aAt» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LatticeLemmas_LocalChangeEq_bAt_of_aAt_bd1074445082
