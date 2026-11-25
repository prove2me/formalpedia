-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_ChainSum_deg_eq_of_linearEquiv_897173931eb1
-- name    : P2M_GroundTheory_Heights__Heights_LatticeLemmas_ChainSum_deg_eq_of_linearEquiv_897173931eb1
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:43:24.058926+00:00
-- url     : https://prove2.me/theorems/f1937ce7-a6f7-47d0-a463-cbaabd24bde3
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Lemmas Chain Sum deg eq of linear Equiv 897173931eb1: P2 M Ground Theory Heights  Heights Lattice Lemmas Chain Sum deg eq of linear Equiv 897173931eb1
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Lemmas Chain Sum deg eq of linear Equiv 897173931eb1 construction uses the P2 M Ground Theory Heights  Heights Lattice Lemmas Chain Sum deg eq of linear Equiv 897173931eb1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PChainSum.lean#L17-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PChainSum.lean#L17-L36

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_LinearIndependentSumElimOfExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PChainSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LatticeLemmas
open NumberField
open GroundTheory.Heights₂.Heights
universe u v
noncomputable section
open GroundTheory.Heights₂.Heights.LatticeLemmas.ChainSum

theorem P2M_GroundTheory_Heights__Heights_LatticeLemmas_ChainSum_deg_eq_of_linearEquiv_897173931eb1 {K : Type u} [Field K] [NumberField K] (A B : HermitianBundle.{v} K)
    (φ : A.carrier ≃ₗ[𝓞 K] B.carrier)
    (hg : ∀ (σ : K →+* ℂ) (n : ℕ) (s : Fin n → A.carrier),
      GroundTheory.Heights₂.Heights.gramDet A.metric σ s =
        GroundTheory.Heights₂.Heights.gramDet B.metric σ (fun i ↦ φ (s i))) :
    A.deg = B.deg := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeLemmas».«ChainSum».«deg_eq_of_linearEquiv» := P2M_GroundTheory_Heights__Heights_LatticeLemmas_ChainSum_deg_eq_of_linearEquiv_897173931eb1
