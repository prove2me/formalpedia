-- Prove2me | Theorems.Thm_SoSLinAlg_WeakRank_proposition_1_10
-- name    : SoSLinAlg.WeakRank.proposition_1_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T22:31:31.132261+00:00
-- url     : https://prove2.me/theorems/70efa038-7bbd-4d8f-8e69-84b1bd149de5
-- title:
--   Proposition 1.10 — all three equal-degree reductions
-- statement:
--   Let $n>r\ge1$ be integers and let $A\in\mathbb R^{n\times n}$ satisfy $\operatorname{rank}A\ge r+1$. The system $\operatorname{WRank}_r^n(A)$ is $XY^\top=A$ in two independent $n\times r$ matrices of unrestricted real indeterminates. Write $\vdash_D S$ for a degree-at-most-$D$ sum-of-squares refutation of the polynomial system $S$, as in Definition 1.1.
--
--   For every nonnegative integer $D$, all three implications hold separately:
--   $$\bigl(\vdash_D\operatorname{WRank}_r^n(A)\Rightarrow\vdash_D\operatorname{WRank}_r^n(I_n)\bigr),$$
--   $$\bigl(\vdash_D\operatorname{WRank}_r^n(I_n)\Rightarrow\vdash_D\operatorname{TFrame}_r^n\bigr),\qquad
--   \bigl(\vdash_D\operatorname{TFrame}_r^n\Rightarrow\vdash_D\operatorname{WPHP}_r^n\bigr).$$
--   Here $I_n$ is the identity matrix, TFrame is $XX^\top=I_n$, and WPHP consists of the Boolean, column-collision, and row-sum equations of Definition 1.8.
--
--   These implications compare refutation degrees across the systems. In particular the first one transports the identity-instance lower bound to every admissible $A$. Each implication has its own premise; the statement is not a single implication conditional on refuting the first system.
--
--   Differences from the source:
--   - encoding: matrix entries indexed by [n] and [r] → entries indexed by Fin n and Fin r, and equations by pairs of indices; reason: zero-based finite indices enumerate precisely the same entries and equations
--   - encoding: the zero polynomial has degree minus infinity → totalDegree 0 = 0 at nonnegative upper bounds; reason: all bounds in this item are nonnegative, so the allowed polynomials are unchanged
-- source:
--   Dmitriy Kunisky, Xifan Yu, The sum-of-squares complexity of linear-algebraic principles, STOC 2027 submission #1181 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1181.pdf, Proposition 1.10, PDF p.6 (printed p.4); proof Appendix A.1, PDF p.37 (printed p.35)

import Mathlib
import Definitions.Def_SoSLinAlg_WeakRank_SoSRefutable
import Definitions.Def_SoSLinAlg_WeakRank_WRank
import Definitions.Def_SoSLinAlg_WeakRank_WPHP

namespace SoSLinAlg.WeakRank

/-- Proposition 1.10, PDF p.6 (printed p.4), proof Appendix A.1, PDF p.37.
All three implications are separate and keep the same degree, including D = 0. -/
theorem proposition_1_10 {n r : ℕ} (hr : 0 < r) (hrn : r < n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : r + 1 ≤ A.rank) :
    ∀ D : ℕ,
      (SoSRefutable (WRank r A) D →
        SoSRefutable (WRank r (1 : Matrix (Fin n) (Fin n) ℝ)) D) ∧
      (SoSRefutable (WRank r (1 : Matrix (Fin n) (Fin n) ℝ)) D →
        SoSRefutable (TFrame n r) D) ∧
      (SoSRefutable (TFrame n r) D → SoSRefutable (WPHP n r) D) := by sorry

end SoSLinAlg.WeakRank
