-- Prove2me | Theorems.Thm_P2M_GroundTheory_ProfCoh___naturality_dbe7f1ebd51e
-- name    : P2M_GroundTheory_ProfCoh___naturality_dbe7f1ebd51e
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:43:12.17205+00:00
-- url     : https://prove2.me/theorems/3ff5ad9b-6e70-4cbf-9458-1dd1a5972954
-- title:
--   P2 M Ground Theory Prof Coh   naturality dbe7f1ebd51e: P2 M Ground Theory Prof Coh   naturality dbe7f1ebd51e
-- statement:
--   The P2 M Ground Theory Prof Coh   naturality dbe7f1ebd51e construction uses the P2 M Ground Theory Prof Coh   naturality dbe7f1ebd51e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/ContinuousCochains/LongExactSequence.lean#L110-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/ContinuousCochains/LongExactSequence.lean#L110-L114

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains_Functoriality
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains_LongExactSequence
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open CategoryTheory ShortComplex
universe u
variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {S₁ S₂ : ShortComplex (Rep.{u} k G)} [IsDiscreteRep S₁.X₁] [IsDiscreteRep S₁.X₂]
  [IsDiscreteRep S₁.X₃] [IsDiscreteRep S₂.X₁] [IsDiscreteRep S₂.X₂] [IsDiscreteRep S₂.X₃]

theorem P2M_GroundTheory_ProfCoh___naturality_dbe7f1ebd51e (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂) (i j : ℕ)
    (hij : i + 1 = j) :
    δ hS₁ i j hij ≫ cohomologyMap φ.τ₁ j = cohomologyMap φ.τ₃ i ≫ δ hS₂ i j hij := by sorry

alias «GroundTheory».«ProfCoh».«δ_naturality» := P2M_GroundTheory_ProfCoh___naturality_dbe7f1ebd51e
