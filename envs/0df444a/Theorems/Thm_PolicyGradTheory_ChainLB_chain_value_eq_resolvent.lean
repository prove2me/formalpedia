-- Prove2me | Theorems.Thm_PolicyGradTheory_ChainLB_chain_value_eq_resolvent
-- name    : PolicyGradTheory.ChainLB.chain_value_eq_resolvent
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T03:32:08.272299+00:00
-- url     : https://prove2.me/theorems/b0853f3c-c3d7-4a1e-93c9-f3331dae6adc
-- title:
--   Appendix B.2, p. 51 — chain value is a resolvent entry
-- statement:
--   Fix the Figure 2 chain with $H\ge1$ and a direct parameter $\theta$ whose three coordinates at each interior state lie strictly between zero and one, with every forward coordinate less than $1/4$. Let $p_i=\theta_{i,a_1}$ and $M^p=(I-\gamma P^p)^{-1}$. Then
--   $$V^{\pi_\theta}(s_0)=M^p_{0,H+1}.$$
--
--   This identifies the discounted return with the matrix entry differentiated in Appendix B.2.
--
--   **Formalization Note** The parameter assumptions are those of Proposition 4.1. The value depends only on the forward coordinates; the other coordinates need not sum to at most one for the algebraic expression to be defined.
-- source:
--   arXiv:1908.00261v5, App. B.2, p. 51, paragraph before Lemma B.1

import Mathlib
import Definitions.Def_PolicyGradTheory_ChainLB_Chain

namespace PolicyGradTheory.ChainLB

/-- Appendix B.2, p. 51: the return from s₀ is the last-column resolvent entry. -/
theorem chain_value_eq_resolvent (H : ℕ) (hH : 1 ≤ H)
    (θ : EuclideanSpace ℝ (Fin H × Fin 3))
    (hθ : ∀ i j, 0 < θ (i, j) ∧ θ (i, j) < 1)
    (hθ1 : ∀ i, θ (i, (0 : Fin 3)) < 1 / 4) :
    chainValue H θ = chainResolvent H (forwardProb H θ) 0 (Fin.last (H + 1)) := by sorry

end PolicyGradTheory.ChainLB
