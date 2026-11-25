-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalPullback_I_pull_eq_1e8439b662ca
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagonalPullback_I_pull_eq_1e8439b662ca
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:26:19.121098+00:00
-- url     : https://prove2.me/theorems/11edccc4-1deb-4c17-b17b-026737389053
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diagonal Pullback I pull eq 1e8439b662ca: P2 M Ground Theory Heights  Heights Inter Diagonal Pullback I pull eq 1e8439b662ca
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diagonal Pullback I pull eq 1e8439b662ca construction uses the P2 M Ground Theory Heights  Heights Inter Diagonal Pullback I pull eq 1e8439b662ca property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagPullI.lean#L58-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagPullI.lean#L58-L134

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagPull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagPullI
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 DiagRAux
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.Inter.DiagonalPullback
variable {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ]

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagonalPullback_I_pull_eq_1e8439b662ca {D : ℕ} (S : ProjectiveLineBundle D)
    (I : Ideal (MRing S.WIdx) → (n : ℕ) → (Fin n → HermLine S.WIdx) → ℝ) (hF : IsIntersectionFamily I)
    (hΔ : IsArithVar S.Diag (D + 1)) (hDP : T.DiagPullStatement (Φ := S.Φ) S.x S.δ S.e S.φ)
    (L : Fin D → HermLine S.WIdx) (hL : ∀ j, IsSmoothHerm (L j))
    (A : HermLine S.YIdx) (A₀ A₁ : HermLine S.WIdx) (d : T.YBlk → ℕ) (hd : ∀ k, A.a k = d k)
    (hA : IsSmoothHerm A) (hp0 : IsPullHerm (diagonalBlockIndex 0) (T.yyEmb 0) A A₀)
    (hp1 : IsPullHerm (diagonalBlockIndex 1) (T.yyEmb 1) A A₁) :
    I S.Diag (D + 1) (Fin.snoc L A₀) = I S.Diag (D + 1) (Fin.snoc L A₁) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagonalPullback».«I_pull_eq» := P2M_GroundTheory_Heights__Heights_Inter_DiagonalPullback_I_pull_eq_1e8439b662ca
