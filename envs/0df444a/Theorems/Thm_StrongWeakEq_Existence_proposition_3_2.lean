-- Prove2me | Theorems.Thm_StrongWeakEq_Existence_proposition_3_2
-- name    : StrongWeakEq.Existence.proposition_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T22:39:33.29407+00:00
-- url     : https://prove2.me/theorems/d18d882c-f85f-4169-930a-c4c44801ab16
-- title:
--   Proposition 3.2, p. 9 — strict first-order dominance (3.21) implies a strong equilibrium
-- statement:
--   Let $f$ satisfy the standing assumptions (2.1)–(2.3) and the conditions of Lemma 3.2 (with time derivative $f_t$ and remainder bound $r$). Let $Q^*\in\mathcal Q$ satisfy
--   $$\Gamma^{Q^*}(Q^*_i)>\Gamma^{Q^*}(Q_i)\qquad\text{for all } i\in S \text{ and } Q\in\mathcal Q \text{ with } Q_i\ne Q^*_i. \tag{3.21}$$
--   Then $Q^*$ is a strong equilibrium (Definition 2.2).
--
--   The condition involves only the first-order gain $\Gamma^{Q^*}$, although its proof needs the second-order expansion (3.16): deviations that agree with $Q^*$ in the current state are only felt at higher order. It is the step from the fixed point to a strong equilibrium in Theorem 3.3.
--
--   **Formalization Note** The expectation $\mathbb E_{i,Q}$ over the chain is written out through its one-dimensional marginals: under a generator $Q$ the law of $X_t$ given $X_0=i$ is the $i$-th row of the matrix exponential $e^{tQ}$, so $\mathbb E_{i,Q}[\int_0^\infty \varphi(t,X_t)\,dt]=\int_0^\infty\sum_j (e^{tQ})_{ij}\varphi(t,j)\,dt$ by Fubini; no Markov process is constructed.
-- source:
--   Huang & Zhou, Strong and Weak Equilibria for Time-Inconsistent Stochastic Control in Continuous Time, arXiv:1809.09243v3, p. 9, Proposition 3.2, (3.21)

import Mathlib
import Definitions.Def_StrongWeakEq_Existence_Model
import Definitions.Def_StrongWeakEq_Existence_SecondOrder

namespace StrongWeakEq.Existence

/-- Proposition 3.2, p. 9: under the conditions of Lemma 3.2, if `Q* ∈ 𝒬` satisfies
`Γ^{Q*}(Q*ᵢ) > Γ^{Q*}(Qᵢ)` for all `i` and `Q ∈ 𝒬` with `Qᵢ ≠ Q*ᵢ` (3.21), then `Q*` is a strong
equilibrium. -/
theorem proposition_3_2 {N : ℕ} (D : Fin N → Set (Fin N → ℝ))
    (f ft : ℝ → Fin N → (Fin N → ℝ) → ℝ) (hS : Standing D f) (hR : SecondOrderReg D f ft)
    (Qs : Matrix (Fin N) (Fin N) ℝ) (hQs : Qs ∈ Controls D)
    (h321 : ∀ i, ∀ Q ∈ Controls D, Q i ≠ Qs i → Gamma f Qs i (Q i) < Gamma f Qs i (Qs i)) :
    IsStrongEquilibrium D f Qs := by sorry

end StrongWeakEq.Existence
