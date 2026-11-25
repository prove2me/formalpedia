-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_orbitCenter_le_of_le_ddb16ad53eae
-- name    : P2M_GroundTheory_Heights__Heights_orbitCenter_le_of_le_ddb16ad53eae
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:49:32.197852+00:00
-- url     : https://prove2.me/theorems/926c00d1-9b66-4125-968b-eff763efa6b1
-- title:
--   P2 M Ground Theory Heights  Heights orbit Center le of le ddb16ad53eae: P2 M Ground Theory Heights  Heights orbit Center le of le ddb16ad53eae
-- statement:
--   The P2 M Ground Theory Heights  Heights orbit Center le of le ddb16ad53eae construction uses the P2 M Ground Theory Heights  Heights orbit Center le of le ddb16ad53eae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitCenterDivSuppLemmas.lean#L96-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitCenterDivSuppLemmas.lean#L96-L201

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCenter
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PHeightRecR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCenterMemIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightSubringPrimeMaximal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCenterDivSuppLemmas
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
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

theorem P2M_GroundTheory_Heights__Heights_orbitCenter_le_of_le_ddb16ad53eae (hMI : OrbitCenterMemIff.Statement)
    (hSP : SubringPrimeMaximal.Statement) (x : Cone n (AlgebraicClosure ℚ)) (hx : BlockNonzero x)
    (v : FinitePlace (coordField x)) (c : (k : ι) → Fin (n k + 1))
    (hc : ∀ k, v (coordVec x k (c k)) = ⨆ i, v (coordVec x k i) ∧ 0 < ⨆ i, v (coordVec x k i))
    (s : MvPolynomial (Coord n) ℤ) (a : ι → ℕ) (hs : Geo.IsMultiHomog (ι := blockIdx n) s a)
    (hsW : s ∉ orbitIdeal x) (Q : Ideal (MvPolynomial (Coord n) ℤ)) [hQp : Q.IsPrime]
    (hWQ : orbitIdeal x ≤ Q) (hsQ : s ∈ Q) (hQv : Q ≤ orbitCenter x v) :
    orbitCenter x v ≤ Q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«orbitCenter_le_of_le» := P2M_GroundTheory_Heights__Heights_orbitCenter_le_of_le_ddb16ad53eae
