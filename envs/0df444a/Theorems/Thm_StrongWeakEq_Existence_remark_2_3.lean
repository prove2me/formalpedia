-- Prove2me | Theorems.Thm_StrongWeakEq_Existence_remark_2_3
-- name    : StrongWeakEq.Existence.remark_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T22:38:38.366129+00:00
-- url     : https://prove2.me/theorems/28d9fc7c-937d-48fa-b9a1-02b5e76a01e2
-- title:
--   Remark 2.3, p. 5 — a strong equilibrium is also a weak one
-- statement:
--   Let $D_i$ be admissible sets and $f$ a payoff rate. If $Q^*\in\mathcal Q$ is a strong equilibrium (Definition 2.2), it is a weak equilibrium (Definition 2.1):
--   $$Q^*\ \text{strong}\ \Longrightarrow\ \liminf_{\varepsilon\downarrow0}\frac{F(i,Q^*)-F(i,Q\otimes_\varepsilon Q^*)}{\varepsilon}\ge0\quad\forall Q\in\mathcal Q,\ i\in S.$$
--
--   The two notions differ: the paper's Example 4.3 exhibits a weak equilibrium that is not strong.
--
--   **Formalization Note** No hypothesis on $D_i$ or $f$ is needed; the statement is about the two definitions only.
-- source:
--   Huang & Zhou, Strong and Weak Equilibria for Time-Inconsistent Stochastic Control in Continuous Time, arXiv:1809.09243v3, p. 5, Remark 2.3 (first sentence)

import Mathlib
import Definitions.Def_StrongWeakEq_Existence_Model

namespace StrongWeakEq.Existence

/-- Remark 2.3, p. 5: a strong equilibrium is also a weak one. -/
theorem remark_2_3 {N : ℕ} (D : Fin N → Set (Fin N → ℝ))
    (f : ℝ → Fin N → (Fin N → ℝ) → ℝ) (Qs : Matrix (Fin N) (Fin N) ℝ)
    (hQs : IsStrongEquilibrium D f Qs) :
    IsWeakEquilibrium D f Qs := by sorry

end StrongWeakEq.Existence
