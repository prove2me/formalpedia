-- Prove2me | Theorems.Thm_SDCA_Lipschitz_lemma_3
-- name    : SDCA.Lipschitz.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:09:56.20598+00:00
-- url     : https://prove2.me/theorems/8cc61f09-a103-419e-b5d0-fadab9315a65
-- title:
--   Lemma 3, p. 15 — the conjugate of an $L$-Lipschitz function is $+\infty$ outside $[-L,L]$
-- statement:
--   Let $\phi:\mathbb R\to\mathbb R$ be $L$-Lipschitz: $|\phi(a)-\phi(b)|\le L|a-b|$ for all $a,b\in\mathbb R$. Let $\phi^*(\alpha)=\sup_z(z\alpha-\phi(z))$ be its convex conjugate. Then
--   $$\phi^*(\alpha)=+\infty\qquad\text{for every }\alpha\text{ with }|\alpha|>L .$$
--
--   Consequently every dual-feasible coordinate of SDCA with $L$-Lipschitz losses lies in $[-L,L]$; this is what bounds the variance term in Lemma 4.
--
--   **Formalization Note** The conjugate is `EReal`-valued and $+\infty$ is `⊤`. No convexity of $\phi$ and no sign condition on $L$ are assumed (a negative $L$ cannot satisfy the Lipschitz inequality).
-- source:
--   Shalev-Shwartz and Zhang, Stochastic Dual Coordinate Ascent Methods for Regularized Loss Minimization, arXiv:1209.1873v2, §7.2, p. 15, Lemma 3

import Mathlib
import Definitions.Def_SDCA_Lipschitz_conj

namespace SDCA.Lipschitz

/-- Lemma 3, p. 15: if `φ : ℝ → ℝ` is `L`-Lipschitz (`|φ(a) − φ(b)| ≤ L|a − b|`), then
`φ*(α) = ∞` for every `α` with `|α| > L`. -/
theorem lemma_3 (φ : ℝ → ℝ) (L : ℝ) (hLip : ∀ a b : ℝ, |φ a - φ b| ≤ L * |a - b|)
    (α : ℝ) (hα : L < |α|) :
    conj φ α = ⊤ := by sorry

end SDCA.Lipschitz
