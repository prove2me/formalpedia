-- Prove2me | Theorems.Thm_UhlmannRoof_RankTwo_lemma_3
-- name    : UhlmannRoof.RankTwo.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:34:24.207099+00:00
-- url     : https://prove2.me/theorems/4de0a016-c615-4b3a-8595-b398f27a4d81
-- title:
--   Lemma 3, p. 6 — compact affine R-sets cover the state space
-- statement:
--   For a supporting affine functional $l_A$, let $\Omega(A)=\{\nu:R(\nu)=l_A(\nu)\}$ within the state space. Then $\Omega(A)$ is a compact, convex $R$-set, and $R$ is affine on it:
--   $$R(t x+(1-t)y)=tR(x)+(1-t)R(y)\quad(x,y\in\Omega(A),\ 0\le t\le1).$$
--   Moreover, every state belongs to the contact set of at least one supporting functional.
--
--   These contact sets are the covering used to define $\Omega_\omega$ at a chosen state.
--
--   **Formalization Note** Every affine functional on the finite dimensional trace one state space is represented by a Hermitian matrix $A$ as in the paper's Remark (9).
-- source:
--   Uhlmann, arXiv:quant-ph/9704017v2, pp. 6–7, Lemma 3 and Remark (9)

import Mathlib
import Definitions.Def_UhlmannRoof_RankTwo_Model

namespace UhlmannRoof.RankTwo

/-- Uhlmann, Lemma 3, p. 6: every supporting contact set is a compact
convex R-set on which R is affine, and the contact sets cover the state space. -/
theorem lemma_3 {d : ℕ} :
    (∀ A : Mat d, SupportsR A →
      IsCompact (OmegaL A) ∧ IsRSet (OmegaL A) ∧
      ∀ x ∈ OmegaL A, ∀ y ∈ OmegaL A, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        R (t • x + (1 - t) • y) = t * R x + (1 - t) * R y) ∧
    (∀ ω : Mat d, IsState ω → ∃ A : Mat d, SupportsR A ∧ ω ∈ OmegaL A) := by sorry

end UhlmannRoof.RankTwo
