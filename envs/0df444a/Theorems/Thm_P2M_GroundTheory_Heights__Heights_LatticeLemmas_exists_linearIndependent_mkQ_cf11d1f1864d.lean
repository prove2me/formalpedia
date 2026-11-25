-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_exists_linearIndependent_mkQ_cf11d1f1864d
-- name    : P2M_GroundTheory_Heights__Heights_LatticeLemmas_exists_linearIndependent_mkQ_cf11d1f1864d
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:35:56.883076+00:00
-- url     : https://prove2.me/theorems/c54e4fc5-0840-5f14-a2e0-5d7cb1f0b966
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Lemmas exists linear Independent mk Q cf11d1f1864d: P2 M Ground Theory Heights  Heights Lattice Lemmas exists linear Independent mk Q cf11d1f1864d
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Lemmas exists linear Independent mk Q cf11d1f1864d construction uses the P2 M Ground Theory Heights  Heights Lattice Lemmas exists linear Independent mk Q cf11d1f1864d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PHadamardMeanQuotient.lean#L24-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PHadamardMeanQuotient.lean#L24-L74

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PHadamardMeanQuotient
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
open NumberField GroundTheory.Heights₂.Heights Submodule Cardinal TensorProduct
universe u v w
noncomputable section
variable {K : Type u} [Field K] [NumberField K]

theorem P2M_GroundTheory_Heights__Heights_LatticeLemmas_exists_linearIndependent_mkQ_cf11d1f1864d (M : HermitianBundle.{v} K) (F : Submodule (𝓞 K) M.carrier)
    {ι : Type w} (x : ι → M.carrier)
    (hx : Module.finrank (𝓞 K) (span (𝓞 K) (Set.range x)) = Module.finrank (𝓞 K) M.carrier) :
    ∃ s : Fin (Module.finrank (𝓞 K) (M.carrier ⧸ F)) → ι,
      LinearIndependent (𝓞 K) (fun j ↦ F.mkQ (x (s j))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeLemmas».«exists_linearIndependent_mkQ» := P2M_GroundTheory_Heights__Heights_LatticeLemmas_exists_linearIndependent_mkQ_cf11d1f1864d
