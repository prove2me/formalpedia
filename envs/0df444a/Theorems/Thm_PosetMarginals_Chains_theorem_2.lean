-- Prove2me | Theorems.Thm_PosetMarginals_Chains_theorem_2
-- name    : PosetMarginals.Chains.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:37:32.783568+00:00
-- url     : https://prove2.me/theorems/e64127b9-4916-4c08-9926-2ea8fcf259f9
-- title:
--   Theorem 2 — exact optimal value of the auxiliary program (Q)
-- statement:
--   Let $P=(X,\preceq)$ be finite and nonempty, and let $\rho_x\in[0,1]$ and $\pi_C\le1$ satisfy conditions (2) and (3). The optimal value of (Q) equals the larger of the greatest element marginal and the greatest maximal-chain target:
--   $$z^*_{\mathcal Q}=\max\!\left\{\max_{x\in X}\rho_x,\ \max_{C\in\mathcal C}\pi_C\right\}.$$
--
--   This exact identity yields the bound needed by Proposition 1 and quantifies the least total subset weight required by the constraints.
--
--   **Formalization Note** The standing assumptions from §2.2 are explicit. The value is the real infimum of feasible objective values, which is proper under these assumptions; the finite maximum uses the nonempty ground set.
-- source:
--   Dahan, Amin & Jaillet, arXiv:1811.08516v3, p. 11, Theorem 2; conclusion p. 19

import Mathlib
import Definitions.Def_PosetMarginals_Chains_Model

namespace PosetMarginals.Chains

/-- Dahan, Amin and Jaillet, Theorem 2, p. 11. -/
theorem theorem_2 {α : Type*} [PartialOrder α] [Fintype α] [Nonempty α]
    (ρ : α → ℝ) (π : Finset α → ℝ) (h : Standing ρ π) :
    zQ ρ π = maxValue ρ π := by sorry

end PosetMarginals.Chains
