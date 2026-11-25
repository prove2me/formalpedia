-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_LocalLatticeIndex_isTorsionFree_1b49b6e7295e
-- name    : P2M_GroundTheory_Heights__Heights_LatticeLemmas_LocalLatticeIndex_isTorsionFree_1b49b6e7295e
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:44:41.552437+00:00
-- url     : https://prove2.me/theorems/0ca00ee0-574e-447f-818b-8ac236eb6c1d
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Lemmas Local Lattice Index is Torsion Free 1b49b6e7295e: P2 M Ground Theory Heights  Heights Lattice Lemmas Local Lattice Index is Torsion Free 1b49b6e7295e
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Lemmas Local Lattice Index is Torsion Free 1b49b6e7295e construction uses the P2 M Ground Theory Heights  Heights Lattice Lemmas Local Lattice Index is Torsion Free 1b49b6e7295e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PLocalLatticeIndex.lean#L55-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PLocalLatticeIndex.lean#L55-L62

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

theorem P2M_GroundTheory_Heights__Heights_LatticeLemmas_LocalLatticeIndex_isTorsionFree_1b49b6e7295e (A : Submodule (v.adicCompletionIntegers K) E) :
    Module.IsTorsionFree (v.adicCompletionIntegers K) A := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeLemmas».«LocalLatticeIndex».«isTorsionFree» := P2M_GroundTheory_Heights__Heights_LatticeLemmas_LocalLatticeIndex_isTorsionFree_1b49b6e7295e
