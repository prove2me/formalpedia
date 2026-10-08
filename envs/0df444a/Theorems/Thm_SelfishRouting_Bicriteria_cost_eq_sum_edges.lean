-- Prove2me | Theorems.Thm_SelfishRouting_Bicriteria_cost_eq_sum_edges
-- name    : SelfishRouting.Bicriteria.cost_eq_sum_edges
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T01:11:20.142488+00:00
-- url     : https://prove2.me/theorems/48ada9bf-cfba-43d9-8ea0-ee3ec0999c2c
-- title:
--   §2.1, p. 7 — edge form of the cost: $C(f) = \sum_e \ell_e(f_e) f_e$
-- statement:
--   Let $A$ be an edge–route incidence matrix, $\ell = (\ell_e)_e$ any family of functions $\mathbb R \to \mathbb R$, and $f = (f_P)_P$ any vector of route flows, with edge flows $f_e = \sum_P A_{eP} f_P$. Then the cost can be computed edge by edge:
--   $$
--   C(f) = \sum_{P} \ell_P(f)\, f_P = \sum_{e} \ell_e(f_e)\, f_e .
--   $$
--
--   The paper uses both forms of the cost throughout; in particular the proof of Theorem 3.1 moves between them.
--
--   **Formalization Note.** The identity is pure algebra and holds for any real matrix $A$, any functions $\ell_e$ and any real $f$; no hypothesis is assumed.
-- source:
--   Roughgarden & Tardos, How Bad is Selfish Routing?, J. ACM 49(2) (2002), author's manuscript of 5 Dec 2001, p. 7, §2.1 (unnumbered display after the definition of C(f))

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SelfishRouting_Bicriteria_Model

namespace SelfishRouting.Bicriteria

open KellyStochasticNetworks

/-- §2.1 (p. 7): the edge form of the cost, `C(f) = ∑ₑ ℓₑ(fₑ) fₑ`. -/
theorem cost_eq_sum_edges {J R : ℕ} (A : Fin J → Fin R → ℝ) (ℓ : Fin J → ℝ → ℝ)
    (x : Fin R → ℝ) :
    cost A ℓ x = ∑ j, ℓ j (linkFlow A x j) * linkFlow A x j := by sorry

end SelfishRouting.Bicriteria
