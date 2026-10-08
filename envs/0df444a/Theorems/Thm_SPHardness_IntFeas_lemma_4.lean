-- Prove2me | Theorems.Thm_SPHardness_IntFeas_lemma_4
-- name    : SPHardness.IntFeas.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:11:46.150228+00:00
-- url     : https://prove2.me/theorems/8b1c99da-370e-440c-80e4-01b0d7a9f30b
-- title:
--   Lemma 4, p. 12 — Ay ≤ b has a binary solution iff it has a solution in ([0, ϵ′] ∪ [1 − ϵ′, 1])ⁿ
-- statement:
--   Let $A\in\mathbb Z^{m\times n}$ and $b\in\mathbb Z^m$ form an Integer Feasibility Problem instance, so $\{y\in\mathbb R^n:Ay\le b\}\subseteq[0,1]^n$. Fix $\epsilon'$ with $0\le\epsilon'<\tfrac12$ and $\epsilon'\sum_j|A_{ij}|<1$ for every row $i$ (that is, $\epsilon'<\min_i\{(\sum_j|A_{ij}|)^{-1}\}$ over the nonzero rows). Then there is a binary vector $y\in\{0,1\}^n$ with $Ay\le b$ if and only if
--   $$\exists\, y\in\big([0,\epsilon']\cup[1-\epsilon',1]\big)^n\ \text{ with }\ Ay\le b .$$
--
--   The lemma says that near-binary solutions of $Ay\le b$ can be rounded to binary ones, because $A$ and $b$ are integral. It is the step that turns a gap in the optimal value of problem (11) into an answer to the Integer Feasibility Problem.
--
--   **Formalization Note.** The page's condition $\epsilon'<\min_i\{(\sum_j|A_{ij}|)^{-1}\}$ is undefined for a zero row of $A$; it is encoded as $\epsilon'\sum_j|A_{ij}|<1$ for every $i$, which agrees with it on nonzero rows and imposes nothing on zero rows (in Lean $(0:\mathbb R)^{-1}=0$, so the literal form would force $\epsilon'<0$). The hypothesis $0\le\epsilon'$ is implicit on the page (otherwise both intervals are empty). The instance condition is inherited from the boxed problem immediately preceding Lemma 4.
-- source:
--   Hanasusanto, Kuhn & Wiesemann, A comment on "computational complexity of stochastic programming problems", Optimization Online preprint 2015/03/4825 (version of October 6, 2015), p. 12, Lemma 4

import Mathlib
import Definitions.Def_SPHardness_IntFeas_Model

open MeasureTheory

namespace SPHardness.IntFeas

theorem lemma_4 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (hinst : IsIFPInstance A b)
    (ε' : ℝ) (hε'0 : 0 ≤ ε') (hε'half : ε' < 1 / 2)
    (hε'row : ∀ i, ε' * ∑ j, |(A i j : ℝ)| < 1) :
    IFPAnswer A b ↔
      ∃ y : Fin n → ℝ, (∀ j, (0 ≤ y j ∧ y j ≤ ε') ∨ (1 - ε' ≤ y j ∧ y j ≤ 1)) ∧
        InPolytope A b y := by sorry

end SPHardness.IntFeas
