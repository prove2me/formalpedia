-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianBundle_degree_eq_of_linearIndependent_05efcbd2008c
-- name    : P2M_GroundTheory_Heights__Heights_HermitianBundle_degree_eq_of_linearIndependent_05efcbd2008c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:25:29.646278+00:00
-- url     : https://prove2.me/theorems/b27527c1-4bfe-44bc-a05e-edfeda537e73
-- title:
--   P2 M Ground Theory Heights  Heights Hermitian Bundle degree eq of linear Independent 05efcbd2008c: P2 M Ground Theory Heights  Heights Hermitian Bundle degree eq of linear Independent 05efcbd2008c
-- statement:
--   The P2 M Ground Theory Heights  Heights Hermitian Bundle degree eq of linear Independent 05efcbd2008c construction uses the P2 M Ground Theory Heights  Heights Hermitian Bundle degree eq of linear Independent 05efcbd2008c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/LinearIndependentSumElimOfExact.lean#L24-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/LinearIndependentSumElimOfExact.lean#L24-L31

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Extension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_LinearIndependentSumElimOfExact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix
open scoped ComplexOrder
noncomputable section
variable {K : Type*} [Field K] [NumberField K]

theorem P2M_GroundTheory_Heights__Heights_HermitianBundle_degree_eq_of_linearIndependent_05efcbd2008c (E : HermitianBundle K)
    (F : Submodule (𝓞 K) E.carrier) {ι : Type*} [Fintype ι] [DecidableEq ι] {s : ι → F}
    (hs : LinearIndependent (𝓞 K) s) (hcard : Fintype.card ι = E.rank F) :
    E.degree F = Real.log (Nat.card (F ⧸ Submodule.span (𝓞 K) (Set.range s))) -
      (1 / 2) * ∑ σ : K →+* ℂ,
        Real.log (GroundTheory.Heights₂.Heights.gramDet E.metric σ (fun i ↦ (s i : E.carrier))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HermitianBundle».«degree_eq_of_linearIndependent» := P2M_GroundTheory_Heights__Heights_HermitianBundle_degree_eq_of_linearIndependent_05efcbd2008c
