-- Prove2me | Theorems.Thm_ValueEquivalence_ve_space_antitone
-- name    : ValueEquivalence.ve_space_antitone
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T17:48:54.494059+00:00
-- url     : https://prove2.me/theorems/f8fde2c5-60ea-485f-9894-d0da96ef8c2b
-- title:
--   Property 3: enlarging the policies or functions shrinks the value-equivalent models
-- statement:
--   Let $S,A$ be finite, $0\le\gamma<1$, $m^*$ the true model and $\mathcal M$ a set of models. Let $\Pi\subseteq\boldsymbol\Pi$ be a set of policies and $\mathcal V$ a set of functions $S\to\mathbb R$. If $\Pi'\subseteq\Pi$ and $\mathcal V'\subseteq\mathcal V$, then
--
--   $$\mathcal M(\Pi,\mathcal V)\subseteq\mathcal M(\Pi',\mathcal V').$$
--
--   Adding policies or functions can only shrink the space of models that are value equivalent to the true model.
-- source:
--   Grimm, Barreto, Singh and Silver, The Value Equivalence Principle for Model-Based Reinforcement Learning, arXiv:2011.03506v1 (2020), Section 3.1, Property 3, p. 3; proof in Appendix A.1.1, p. 13

import Mathlib
import Definitions.Def_ValueEquivalence_Basic

open Filter Topology

namespace ValueEquivalence

theorem ve_space_antitone {S A : Type*} [Fintype S] [Fintype A]
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (M : Set (Model S A)) (mstar : Model S A)
    (Pol Pol' : Set (S → A → ℝ)) (V V' : Set (S → ℝ)) (hPol : Pol ⊆ policies)
    (hPol' : Pol' ⊆ Pol) (hV' : V' ⊆ V) :
    veSpace γ M mstar Pol V ⊆ veSpace γ M mstar Pol' V' := by sorry

end ValueEquivalence
