-- Prove2me | Theorems.Thm_SubsetConvFPRAS_proposition_1_22
-- name    : SubsetConvFPRAS.proposition_1_22
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:19:46.835658+00:00
-- url     : https://prove2.me/theorems/1174ebd2-6d24-4226-8740-e5647088381c
-- title:
--   Proposition 1.22 — fractional log-concavity gives curvature $1-\alpha^{-1}$ after translation
-- statement:
--   Let $p=g_\mu$ be a nonzero multiaffine polynomial with nonnegative coefficients $\mu$, and let $0<\alpha\le1$. If $p$ is $\alpha$-fractionally log-concave, i.e. $x\mapsto\log p(x_1^\alpha,\dots,x_n^\alpha)$ is concave on $\mathbb R^U_{>0}$, then the coefficient measure $\hat\mu$ of $p(1+x)$,
--   $$\hat\mu(S)=\sum_{A\supseteq S}\mu(A),$$
--   has downward-closed support and upward $(1-\alpha^{-1})$-spectral curvature.
--
--   At $\alpha=1$ (log-concavity) this gives zero curvature for the translated measure, which is Observation 5.8 for $w_\lambda$ and the input to Corollary 5.7.
--
--   Differences from the source:
--   - encoding: a multiaffine polynomial p → its coefficient weight μ, with p = g_μ; reason: a multiaffine polynomial is determined by its coefficients
-- source:
--   Chen, Liu, An FPRAS for Counting Common Bases of Two Matroids, arXiv:2610.06724 (version held, sha256 6c1d68c2…919476), Definition 1.21 and Proposition 1.22, p.8 (proof pp.39–40)

import Mathlib
import Definitions.Def_SubsetConvFPRAS_SetWeights

open scoped Classical

namespace SubsetConvFPRAS

/-- Chen, Liu, arXiv:2610.06724 (sha256 6c1d68c2…), Proposition 1.22, p.8. Let `p = g_μ` be nonzero,
multiaffine and `α`-fractionally log-concave with nonnegative coefficients, `0 < α ≤ 1`. Then the coefficient
measure `μ̂` of `p(1 + x)` has downward-closed support and upward `(1 - α⁻¹)`-spectral curvature.

**Formalization Note.** A multiaffine polynomial is given by its coefficient weight `μ`. -/
theorem proposition_1_22 {U : Type} [Fintype U] [DecidableEq U] (μ : Finset U → ℝ)
    (hμ : ∀ S, 0 ≤ μ S) (α : ℝ) (hα : 0 < α) (hα' : α ≤ 1) (hflc : IsFractionallyLogConcave α μ) :
    HasDownwardClosedSupport (translateUp μ) ∧ HasCurv (translateUp μ) (1 - α⁻¹) := by sorry

end SubsetConvFPRAS
