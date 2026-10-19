-- Prove2me | Theorems.Thm_UnphysicalHilbert_prop20_domain_not_complete
-- name    : UnphysicalHilbert.prop20_domain_not_complete
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T21:06:49.034748+00:00
-- url     : https://prove2.me/theorems/e8c80cb1-18c5-40f4-8432-04ec08ff16b7
-- title:
--   Proposition 20 — the domain of an unbounded closed operator is not complete
-- statement:
--   Let $H$ and $Y$ be complex Hilbert spaces and let $X:D(X)\subseteq H\to Y$ be a linear operator defined on a subspace $D(X)$ of $H$. Assume that $X$ is **closed** (its graph is closed in $H\times Y$) and **unbounded**: there is no constant $C$ with $\|Xx\|\le C\|x\|$ for all $x\in D(X)$. Then the inner product space $D(X)$, with the norm of $H$, is not complete.
--
--   Completeness of the state space is incompatible with having an unbounded observable defined on every state.
--
--   **Formalization Note** The paper does not state a hypothesis on $X$ beyond unboundedness, but its proof appeals to the converse of the Hellinger–Toeplitz theorem, and without a hypothesis of this kind the statement is false (a discontinuous linear functional defined on all of $H$ has a complete domain). Closedness is the standard hypothesis covering self-adjoint operators such as position and momentum.
-- source:
--   G. Carcassi, C. A. Aidala, F. Calderón, *The unphysicality of Hilbert spaces*, arXiv:2308.06669v3 [quant-ph], 22 Dec 2024, https://arxiv.org/abs/2308.06669, Section VI, pp. 10–11, Proposition 20 (closedness added, see note)

import Mathlib

namespace UnphysicalHilbert

/-- Proposition 20: the domain of an unbounded closed operator between Hilbert spaces is
an inner product space that is not complete. -/
theorem prop20_domain_not_complete
    {H Y : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    (X : H →ₗ.[ℂ] Y) (hX : X.IsClosed)
    (hunb : ¬ ∃ C : ℝ, ∀ x : X.domain, ‖X x‖ ≤ C * ‖(x : H)‖) :
    ¬ CompleteSpace X.domain := by
  sorry

end UnphysicalHilbert
