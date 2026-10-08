-- Prove2me | Theorems.Thm_RobustDP_Discounted_theorem5a_contraction
-- name    : RobustDP.Discounted.theorem5a_contraction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:45:34.896979+00:00
-- url     : https://prove2.me/theorems/cd7c09a2-750a-488d-b225-ee0cdea129f1
-- title:
--   Theorem 5(a) — the robust Bellman operator L_D maps V into V and is a λ-contraction
-- statement:
--   Let $(\mathcal S,\mathcal A,\mathcal P,r,\lambda)$ be a discounted ambiguous MDP and let $\mathcal D$ be any nonempty set of deterministic Markov decision rules. Then $\mathcal L_{\mathcal D}$ maps bounded functions to bounded functions, and for all bounded $U,V:\mathcal S\to\mathbb R$,
--   $$\|\mathcal L_{\mathcal D}U-\mathcal L_{\mathcal D}V\|\le\lambda\,\|U-V\|.$$
--
--   Since $\lambda<1$, $\mathcal L_{\mathcal D}$ is a contraction of the Banach space $(\mathbf V,\|\cdot\|)$; this is the input to the Banach fixed point argument of Theorem 5(b).
--
--   **Formalization Note** $\mathcal D$ is an arbitrary nonempty set of rules, as on the page ("Let $\mathcal D$ be any subset"); nonemptiness excludes the empty supremum. $\|\cdot\|$ is the supremum norm.
-- source:
--   Iyengar, Robust dynamic programming, CORC Tech Report TR-2002-07 (rev. May 4, 2004), p. 9, Theorem 5(a), eq. (23)

import Mathlib
import Definitions.Def_RobustDP_Discounted_Model
import Definitions.Def_RobustDP_Discounted_Value
import Definitions.Def_RobustDP_Discounted_Bellman

namespace RobustDP.Discounted

theorem theorem5a_contraction {S A : Type*} [Countable S] [Countable A] (M : Model S A)
    (D : Set (DecisionRule M)) (hD : D.Nonempty) (U W : S → ℝ) (hU : IsBounded U)
    (hW : IsBounded W) :
    IsBounded (L M D U) ∧
      supNorm (fun s => L M D U s - L M D W s) ≤ M.lam * supNorm (fun s => U s - W s) := by sorry

end RobustDP.Discounted
