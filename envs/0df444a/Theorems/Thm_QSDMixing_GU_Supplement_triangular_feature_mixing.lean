-- Prove2me | Theorems.Thm_QSDMixing_GU_Supplement_triangular_feature_mixing
-- name    : QSDMixing.GU.Supplement.triangular_feature_mixing
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T04:42:16.853195+00:00
-- url     : https://prove2.me/theorems/21114454-9d71-41dd-95c5-604bbfde16bc
-- title:
--   Theorem 6 (corrected: integer ceiling in eq. (25)) — triangular Fourier mixing bound
-- statement:
--   Let $X_1,\ldots,X_n$ be independent finite random variables and let $\Phi$ be triangular with target $\widehat A=B_1\times\cdots\times B_n$. For each $i$, define
--
--   $$
--   \lambda_i=\max_{\chi\in\widehat B_i\setminus\{1\}}
--     \mathbb E_{X_{<i}}\left|\mathbb E_{X_i}\chi(\Phi_i(X_{\le i}))\right|^2.
--   $$
--
--   Then for every integer $t>1$,
--
--   $$
--   d_{\mathrm{TV}}(\operatorname{Law}(Z_t),\operatorname{Unif}(\widehat A))
--     \le\frac12\sum_{i=1}^n\sqrt{(|B_i|-1)\lambda_i^t}.
--   $$
--
--   Put $\lambda=\max_i\lambda_i$ and $r=\max_i\log|B_i|$. For $0<\lambda<1$, the resulting integer mixing-time bound is
--
--   $$
--   t_{\min}(\epsilon)\le\left\lceil\frac{r+2\log(n/\epsilon)}{-\log\lambda}\right\rceil.
--   $$
--
--   At $\lambda=0$, the displayed total-variation estimate gives $t_{\min}\le2$; at $\lambda=1$ it yields no finite upper bound.
--
--   Differences from the source:
--   - correction: equation (25) states $t_{\min}\le(r+2\log(n/\epsilon))/(-\log\lambda)$ without integer rounding → Lean takes the natural-number ceiling, uses the time-two consequence at $\lambda=0$, and returns $\infty$ at $\lambda=1$; reason: for $n=1$, $B_1=\mathbb Z_2$, $p(0)=5/8$, $p(1)=3/8$, and $\epsilon=1/10$, one has $\lambda=1/16$ and $t_{\min}=2$ but the printed right side $(\log2+2\log10)/\log16$ is less than $2$
--   - encoding: independent coordinates $X_i$ → a product of finite marginal probability laws; reason: product mass is exactly finite-coordinate independence
--   - encoding: conditional expectations in equation (23) → nested finite sums over an outer and an independent inner source vector, with the $i$th coordinate replaced; reason: triangularity makes later coordinates irrelevant and the sums are the two expectations in the displayed order
--   - encoding: a maximum over nontrivial characters of a trivial factor → supremum of the finite set, assigned zero when the set is empty; reason: the corresponding $|B_i|-1$ term is zero and no mixing obstruction is present
-- source:
--   Zhou, Leditzky, A mixing time method for estimating the sample complexity of quantum state discrimination, arXiv:2609.40182 (held version, sha256 62fb68dd…), Theorem 6, p.25, eqs. (23)–(25)

import Mathlib
import Definitions.Def_QSDMixing_GU_Supplement_TriangularWalk

set_option autoImplicit false

namespace QSDMixing.GU.Supplement

/-- **Theorem 6, p.25 (corrected integer bound).** The conditional Fourier biases of an
independent-coordinate triangular feature map control total variation at every integer `t>1`.
The mixing-time consequence uses the ceiling of the printed real threshold, with the endpoint
`λ=0` handled by the same `t=2` estimate and `λ=1` assigned no finite bound.

Zhou, Leditzky, *A mixing time method for estimating the sample complexity of quantum state
discrimination*, arXiv:2609.40182 (held version, sha256 62fb68dd…), Theorem 6, p.25,
eqs. (23)--(25).

**Formalization Note.** Equation (25) as printed omits integer rounding. For one coordinate
`B=Z/2Z`, increment law `p(0)=5/8`, `p(1)=3/8`, and `ε=1/10`, one has `λ=1/16` and
`t_min=2`, whereas the printed right side is `(log 2 + 2 log 10)/log 16 < 2`. The ceiling is
therefore a necessary correction, not a weakening. -/
theorem triangular_feature_mixing (n : ℕ) (hn : 0 < n) (W : TriangularWalk n) :
    (∀ t : ℕ, 1 < t →
      W.tv t ≤ (1 / 2 : ℝ) *
        ∑ i, Real.sqrt (((Fintype.card (W.Target i) : ℝ) - 1) * (W.lambda i) ^ t)) ∧
    ∀ ε : ℝ, 0 < ε → ε < 1 →
      W.mixingTime ε ≤ W.mixingBound ε := by sorry

end QSDMixing.GU.Supplement
