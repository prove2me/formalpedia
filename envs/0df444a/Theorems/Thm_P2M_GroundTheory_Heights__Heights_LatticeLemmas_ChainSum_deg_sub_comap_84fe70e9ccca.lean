-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_ChainSum_deg_sub_comap_84fe70e9ccca
-- name    : P2M_GroundTheory_Heights__Heights_LatticeLemmas_ChainSum_deg_sub_comap_84fe70e9ccca
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:43:53.920012+00:00
-- url     : https://prove2.me/theorems/2cf3afd5-6097-4260-9078-00445daca835
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Lemmas Chain Sum deg sub comap 84fe70e9ccca: P2 M Ground Theory Heights  Heights Lattice Lemmas Chain Sum deg sub comap 84fe70e9ccca
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Lemmas Chain Sum deg sub comap 84fe70e9ccca construction uses the P2 M Ground Theory Heights  Heights Lattice Lemmas Chain Sum deg sub comap 84fe70e9ccca property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PChainSum.lean#L43-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PChainSum.lean#L43-L53

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

theorem P2M_GroundTheory_Heights__Heights_LatticeLemmas_ChainSum_deg_sub_comap_84fe70e9ccca {K : Type u} [Field K] [NumberField K] (M : HermitianBundle.{v} K)
    {F G : Submodule (𝓞 K) M.carrier} (hGF : G ≤ F) :
    ((M.sub F).sub (G.comap F.subtype)).deg = (M.sub G).deg := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeLemmas».«ChainSum».«deg_sub_comap» := P2M_GroundTheory_Heights__Heights_LatticeLemmas_ChainSum_deg_sub_comap_84fe70e9ccca
