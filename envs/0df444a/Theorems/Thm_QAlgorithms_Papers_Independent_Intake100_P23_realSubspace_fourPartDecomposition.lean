-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P23_realSubspace_fourPartDecomposition
-- name    : QAlgorithms.Papers.Independent.Intake100.P23.realSubspace_fourPartDecomposition
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:17:09.122269+00:00
-- url     : https://prove2.me/theorems/62c74ffb-df4c-4f46-a24c-23ea88ea0138
-- title:
--   Canonical four-part decomposition of a closed real subspace
-- statement:
--   Let $V$ be a closed real subspace of a complex Hilbert space $F$. All complements below are real unless a complex subspace is specified. Set
--   $$F_+=V\cap iV,\quad F_-=V^{\perp_{\mathbb R}}\cap(iV)^{\perp_{\mathbb R}},\quad F_1=(V\cap iV^{\perp_{\mathbb R}})+(iV\cap V^{\perp_{\mathbb R}}),$$
--   $$F_0=(F_++F_-+F_1)^\perp.$$
--   These are complex, pairwise orthogonal closed subspaces and $F=F_+\oplus F_0\oplus F_1\oplus F_-$. Moreover $V\cap F_+=F_+$ and $V\cap F_-=\{0\}$. Put $V_0=V\cap F_0$ and $V_1=V\cap F_1=V\cap iV^{\perp_{\mathbb R}}$. Then $V_0$ is in general position inside $F_0$ and
--   $$V=F_+\oplus V_0\oplus V_1\oplus\{0\},\qquad iV^{\perp_{\mathbb R}}=\{0\}\oplus i(V_0^{\perp_{\mathbb R}}\cap F_0)\oplus V_1\oplus F_-.$$
--   General position means all three intersections from Theorem 51 vanish, using complements internal to $F_0$. This separates the complex, generic, real, and absent components. **Formalization Note** The self-referential final $F_0$ in the printed definition is corrected to $F_1$, as explicitly authorized by the plan and forced by the subsequent decompositions. The correction is independently checked in MODERATION-r1.md.
-- source:
--   Introduction to representations of the canonical commutation and anticommutation relations, arXiv:math-ph/0511030v2, PDF p. 61, Theorem 52

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P23

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P23

open QAlgorithms.Papers.Independent.Renew46.P03 (tensorVector)

variable {Y : Type*} [AddCommGroup Y] [Module ℝ Y]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section FourPartDecomposition

open scoped ClosedSubmodule

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- PDF p.61, Theorem 52, with the documented W_0-to-W_1 referent correction.
Pairwise orthogonality and total span encode the Hilbert direct sum; all parts
are computed from V rather than free variables satisfying the conclusion. -/
theorem realSubspace_fourPartDecomposition (V : ClosedSubmodule ℝ F) :
    (∀ j, ComplexInvariant (decompositionPieces V j)) ∧
    (∀ j k, j ≠ k → decompositionPieces V j ≤ (decompositionPieces V k)ᗮ) ∧
    (⨆ j, decompositionPieces V j) = ⊤ ∧
    V ⊓ decompositionPlus V = decompositionPlus V ∧
    V ⊓ decompositionMinus V = ⊥ ∧
    V ⊓ decompositionOne V = V ⊓ V.symplComp ∧
    GeneralPositionIn (V ⊓ decompositionZero V) (decompositionZero V) ∧
    V = decompositionPlus V ⊔ (V ⊓ decompositionZero V) ⊔ (V ⊓ decompositionOne V) ∧
    V.symplComp = (decompositionZero V ⊓ (V ⊓ decompositionZero V)ᗮ).mulI ⊔
      (V ⊓ decompositionOne V) ⊔ decompositionMinus V := by sorry

end FourPartDecomposition

end QAlgorithms.Papers.Independent.Intake100.P23

end
