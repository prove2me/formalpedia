-- Prove2me | Theorems.Thm_VectorSpaceOpt_min_norm_alignment_criterion
-- name    : VectorSpaceOpt.min_norm_alignment_criterion
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-24T15:52:36.670425+00:00
-- url     : https://prove2.me/theorems/9072f9a7-8398-4905-b771-a7eed4f75953
-- title:
--   Alignment characterizes best approximations
-- statement:
--   Let $M$ be a subspace of a real normed vector space $X$ and let $x \in X$ lie **outside the closure of $M$**. Then a vector $m_0 \in M$ is a best approximation to $x$ from $M$,
--
--   $$\|x - m_0\| \le \|x - m\| \qquad \text{for all } m \in M,$$
--
--   **if and only if** there is a **nonzero** functional $x^* \in M^\perp$ **aligned** with the error $x - m_0$, that is, with
--
--   $$\langle x - m_0,\, x^*\rangle = \|x^*\|\,\|x - m_0\|.$$
--
--   This is the projection theorem's orthogonality criterion transported to a normed space. In Hilbert space the two coincide: a functional in $M^\perp$ aligned with $x - m_0$ is represented by a nonnegative multiple of $x - m_0$, which forces $x - m_0 \perp M$.
--
--   What is lost in the transition is uniqueness. In $\mathbb{R}^2$ under the supremum norm, with $M$ the horizontal axis and $x = (2,1)$, the minimum distance is $1$ and *every* $m = (\alpha, 0)$ with $1 \le \alpha \le 3$ attains it. The criterion above characterizes each of them; it does not single one out.
--
--   **Formalization Note.** The source states this for an arbitrary subspace. The hypothesis $x \notin \overline{M}$ is added because the "only if" direction fails literally in the degenerate case of a dense proper subspace containing $x$: there $m_0 = x$ minimizes but $M^\perp = \{0\}$ holds no nonzero functional. Outside that case the hypothesis is exactly what the source's own proof uses. Alignment is stated through the published `aligned` definition, with no normalization imposed on $x^*$.
-- source:
--   David G. Luenberger, Optimization by Vector Space Methods, John Wiley & Sons, 1969, §5.8, Corollary 1, pp. 120–121

import Mathlib
import Definitions.Def_VectorSpaceOpt_aligned

namespace VectorSpaceOpt

theorem min_norm_alignment_criterion {X : Type} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (M : Submodule ℝ X) (x : X)
    (hx : x ∉ closure (M : Set X)) (m₀ : X) (hm₀ : m₀ ∈ M) :
    (∀ m ∈ M, ‖x - m₀‖ ≤ ‖x - m‖) ↔
    ∃ f : X →L[ℝ] ℝ, f ≠ 0 ∧ (∀ m ∈ M, f m = 0) ∧
      VectorSpaceOpt_aligned (x - m₀) f := by sorry

end VectorSpaceOpt
