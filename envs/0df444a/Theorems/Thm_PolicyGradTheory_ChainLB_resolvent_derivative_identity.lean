-- Prove2me | Theorems.Thm_PolicyGradTheory_ChainLB_resolvent_derivative_identity
-- name    : PolicyGradTheory.ChainLB.resolvent_derivative_identity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T03:32:19.668306+00:00
-- url     : https://prove2.me/theorems/1552a139-d804-4ae2-9934-554dcd4f0666
-- title:
--   Equation (32), p. 54 — derivative of the chain resolvent
-- statement:
--   Fix a chain with $H\ge1$, forward probabilities $0<p_i<1$, and $M^p=(I-\gamma P^p)^{-1}$. For states $a,b$ and an interior state $h\in\{1,\ldots,H\}$, the derivative in its forward probability is
--   $$\frac{\partial M^p_{a,b}}{\partial p_h}=\gamma M^p_{a,h}\bigl(M^p_{h+1,b}-M^p_{h-1,b}\bigr).$$
--
--   This is the entrywise derivative identity used to bound all higher order partial derivatives in Appendix B.2.
--
--   **Formalization Note** The displayed identity is the sign-rearranged form of the paper's equation (32), which writes its negative on both sides. The input $p$ is restricted to the open probability cube, where the resolvent is nonsingular.
-- source:
--   arXiv:1908.00261v5, App. B.2, (32), p. 54

import Mathlib
import Definitions.Def_PolicyGradTheory_ChainLB_Chain

namespace PolicyGradTheory.ChainLB

/-- Appendix B.2, (32), p. 54: derivative of one resolvent entry in an interior forward probability. -/
theorem resolvent_derivative_identity (H : ℕ) (hH : 1 ≤ H)
    (p : Fin H → ℝ) (hp : ∀ i, 0 < p i ∧ p i < 1)
    (a b : Fin (H + 2)) (i : Fin H) :
    fderiv ℝ (fun q : Fin H → ℝ => chainResolvent H q a b) p (Pi.single i (1 : ℝ)) =
      chainGamma H * chainResolvent H p a ⟨i.val + 1, by omega⟩ *
        (chainResolvent H p ⟨i.val + 2, by omega⟩ b -
         chainResolvent H p ⟨i.val, by omega⟩ b) := by sorry

end PolicyGradTheory.ChainLB
