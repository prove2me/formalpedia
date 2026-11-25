-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_BlockTrdeg_algebraicIndependent_forgotten_1e622b88ee59
-- name    : P2M_GroundTheory_Heights__Heights_BlockTrdeg_algebraicIndependent_forgotten_1e622b88ee59
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:16:24.675607+00:00
-- url     : https://prove2.me/theorems/5786bd24-7a11-4a92-8ebe-92967829dea7
-- title:
--   P2 M Ground Theory Heights  Heights Block Trdeg algebraic Independent forgotten 1e622b88ee59: P2 M Ground Theory Heights  Heights Block Trdeg algebraic Independent forgotten 1e622b88ee59
-- statement:
--   The P2 M Ground Theory Heights  Heights Block Trdeg algebraic Independent forgotten 1e622b88ee59 construction uses the P2 M Ground Theory Heights  Heights Block Trdeg algebraic Independent forgotten 1e622b88ee59 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PBlockTrdeg.lean#L142-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PBlockTrdeg.lean#L142-L202

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsBlockTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PBlockTrdeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 Algebra Cardinal
open GroundTheory.Heights₂.Heights.BlockTrdeg
attribute [local instance] MvPolynomial.weightedGradedAlgebra
open scoped Classical
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')}
  {L : Type} [Field L] [Algebra ℚ L] {φ : MRing ι' →+* L}
omit [Fintype K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_BlockTrdeg_algebraicIndependent_forgotten_1e622b88ee59 (hv : ∀ p, (v p).1 = κ p.1) (hP : IsMultiHomogIdeal P')
    (hprime : P'.IsPrime) (hker : RingHom.ker φ = P') (i : ∀ k : Forgotten κ, ι' k.1)
    (hi : ∀ k, (X ⟨k.1, i k⟩ : MRing ι') ∉ P') (S : Subalgebra ℚ L)
    (hS : S ≤ adjoin ℚ (Set.range fun p : Σ k, ι k ↦ φ (X (v p)))) :
    AlgebraicIndependent S (fun k : Forgotten κ ↦ φ (X ⟨k.1, i k⟩)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«BlockTrdeg».«algebraicIndependent_forgotten» := P2M_GroundTheory_Heights__Heights_BlockTrdeg_algebraicIndependent_forgotten_1e622b88ee59
