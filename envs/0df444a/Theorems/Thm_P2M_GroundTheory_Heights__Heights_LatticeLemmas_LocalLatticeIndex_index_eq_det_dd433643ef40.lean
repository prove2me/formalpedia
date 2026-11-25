-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_LocalLatticeIndex_index_eq_det_dd433643ef40
-- name    : P2M_GroundTheory_Heights__Heights_LatticeLemmas_LocalLatticeIndex_index_eq_det_dd433643ef40
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:43:25.719884+00:00
-- url     : https://prove2.me/theorems/1adaaed7-db4c-4862-8fc3-a029a443c865
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Lemmas Local Lattice Index index eq det dd433643ef40: P2 M Ground Theory Heights  Heights Lattice Lemmas Local Lattice Index index eq det dd433643ef40
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Lemmas Local Lattice Index index eq det dd433643ef40 construction uses the P2 M Ground Theory Heights  Heights Lattice Lemmas Local Lattice Index index eq det dd433643ef40 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PLocalLatticeIndex.lean#L64-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PLocalLatticeIndex.lean#L64-L172

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsLocalLatticeIndex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PLocalLatticeIndex
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
open NumberField IsDedekindDomain TensorProduct Module
noncomputable section
variable {K : Type*} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}
  {E : Type*} [AddCommGroup E] [Module (v.adicCompletion K) E]
  [Module (v.adicCompletionIntegers K) E]
  [IsScalarTower (v.adicCompletionIntegers K) (v.adicCompletion K) E]

theorem P2M_GroundTheory_Heights__Heights_LatticeLemmas_LocalLatticeIndex_index_eq_det_dd433643ef40 (A B : Submodule (v.adicCompletionIntegers K) E)
    (g : E ≃ₗ[v.adicCompletion K] E) (hfg : A.FG)
    (hsp : Submodule.span (v.adicCompletion K) (A : Set E) = ⊤)
    (hB : (B : Set E) = g '' A) (hBA : B ≤ A) :
    (B.toAddSubgroup.relIndex A.toAddSubgroup : ℝ) =
      ‖LinearMap.det (g : E →ₗ[v.adicCompletion K] E)‖⁻¹ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeLemmas».«LocalLatticeIndex».«index_eq_det» := P2M_GroundTheory_Heights__Heights_LatticeLemmas_LocalLatticeIndex_index_eq_det_dd433643ef40
