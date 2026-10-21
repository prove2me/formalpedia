-- Prove2me | Theorems.Thm_PosetMarginals_Chains_proposition_1
-- name    : PosetMarginals.Chains.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:37:34.867966+00:00
-- url     : https://prove2.me/theorems/f0b3e029-ae91-4368-aa1c-a2d5b789b821
-- title:
--   Proposition 1 — feasibility of (D) is equivalent to the bound on (Q)
-- statement:
--   Let $P=(X,\preceq)$ be finite and nonempty, with element marginals $\rho_x\in[0,1]$ and maximal-chain targets $\pi_C\le1$ satisfying conditions (2) and (3). Let $z^*_{\mathcal Q}$ be the optimal objective value of the auxiliary program (Q). Then
--   $$(\mathcal D)\text{ is feasible}\quad\Longleftrightarrow\quad z^*_{\mathcal Q}\le1.$$
--
--   This converts the distribution-existence question into a bound on an optimization problem without the normalization constraint.
--
--   **Formalization Note** The standing assumptions guarantee that (Q) has feasible points and a finite lower bound, so the real infimum represents its optimal value.
-- source:
--   Dahan, Amin & Jaillet, arXiv:1811.08516v3, p. 10, Proposition 1

import Mathlib
import Definitions.Def_PosetMarginals_Chains_Model

namespace PosetMarginals.Chains

/-- Dahan, Amin and Jaillet, Proposition 1, p. 10. -/
theorem proposition_1 {α : Type*} [PartialOrder α] [Fintype α] [Nonempty α]
    (ρ : α → ℝ) (π : Finset α → ℝ) (h : Standing ρ π) :
    ProblemD ρ π ↔ zQ ρ π ≤ 1 := by sorry

end PosetMarginals.Chains
