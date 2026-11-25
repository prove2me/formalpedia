-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LatticeLemmas_LocalChangeEq_span_map_95ae8807c50b
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LatticeLemmas_LocalChangeEq_span_map_95ae8807c50b
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:44:45.886041+00:00
-- url     : https://prove2.me/theorems/15b8144f-fd58-4aa6-858d-a9df13ef7b97
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Lattice Lemmas Local Change Eq span map 95ae8807c50b: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Lattice Lemm
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Lattice Lemmas Local Change Eq span map 95ae8807c50b construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Lattice Lemmas Local Change Eq span map 95ae8807c50b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/LocalChangeOfVectorSpace.lean#L141-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/LocalChangeOfVectorSpace.lean#L141-L146

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LatticeLemmas_LocalChangeEq_span_map_95ae8807c50b (L : Submodule (𝓞 K) V) (hL : Submodule.span K (L : Set V) = ⊤) :
    Submodule.span K ((L.map (intEquiv φ).toLinearMap : Submodule (𝓞 K) (Fin r → K)) :
      Set (Fin r → K)) = ⊤ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«LatticeLemmas».«LocalChangeEq».«span_map» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LatticeLemmas_LocalChangeEq_span_map_95ae8807c50b
