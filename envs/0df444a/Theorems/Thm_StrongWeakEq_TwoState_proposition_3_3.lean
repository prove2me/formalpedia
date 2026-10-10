-- Prove2me | Theorems.Thm_StrongWeakEq_TwoState_proposition_3_3
-- name    : StrongWeakEq.TwoState.proposition_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T23:33:00.915196+00:00
-- url     : https://prove2.me/theorems/cbc7c32f-ca09-456e-8842-8a2c7d0b485d
-- title:
--   Proposition 3.3, p. 9 — the second-order test: the sign of Λ^{Q*}(i,Q*) − Λ^{Q*}(i,Q) on R decides strong equilibrium
-- statement:
--   Let $f$ satisfy the standing assumptions of §2 and the conditions of Lemma 3.2 (with time derivative $f_t$), and let $Q^*\in\mathcal Q$ be a weak equilibrium. Consider
--   $$
--   R:=\{(i,Q)\in S\times\mathcal Q\setminus\{Q^*\}:\ \Gamma^{Q^*}(Q^*_i)=\Gamma^{Q^*}(Q_i)\}. \tag{3.22}
--   $$
--   1. If $\Lambda^{Q^*}(i,Q^*)>\Lambda^{Q^*}(i,Q)$ for all $(i,Q)\in R$, then $Q^*$ is a strong equilibrium.
--   2. If $\Lambda^{Q^*}(i,Q^*)<\Lambda^{Q^*}(i,Q)$ for some $(i,Q)\in R$, then $Q^*$ is not a strong equilibrium.
--
--   Here $\Lambda^{Q^*}(i,Q)=f_t(0,i,Q_i)+Q_i\cdot(2G(Q^*)+\Gamma^{Q^*}(Q))$ is the second-order coefficient (3.17). When the first-order condition (3.10) holds with equality, this proposition decides strong equilibrium; Example 4.3 uses the second part.
--
--   **Formalization Note** $\mathcal Q\setminus\{Q^*\}$ excludes the generator $Q=Q^*$ itself, not the rows with $Q_i=Q^*_i$; the Lean quantifies over $Q\in\mathcal Q$ with $Q\ne Q^*$ exactly so. The conditions of Lemma 3.2 are the predicate `SecondOrderReg`, with $f_t$ a witness tied to $f$ by its derivative.
-- source:
--   Huang & Zhou, Strong and Weak Equilibria for Time-Inconsistent Stochastic Control in Continuous Time, arXiv:1809.09243v3, p. 9, Proposition 3.3, (3.22)

import Mathlib
import Definitions.Def_StrongWeakEq_Existence_Model
import Definitions.Def_StrongWeakEq_Existence_SecondOrder

namespace StrongWeakEq.TwoState

/-- Proposition 3.3, p. 9: let `f` satisfy the conditions of Lemma 3.2 and let `Q*` be a weak
equilibrium; with `R = {(i, Q) ∈ S × 𝒬 \ {Q*} : Γ^{Q*}(Q*ᵢ) = Γ^{Q*}(Qᵢ)}` (3.22): if
`Λ^{Q*}(i, Q*) > Λ^{Q*}(i, Q)` on all of `R`, then `Q*` is a strong equilibrium; if
`Λ^{Q*}(i, Q*) < Λ^{Q*}(i, Q)` for some `(i, Q) ∈ R`, then `Q*` is not a strong equilibrium. -/
theorem proposition_3_3 {N : ℕ} (D : Fin N → Set (Fin N → ℝ))
    (f ft : ℝ → Fin N → (Fin N → ℝ) → ℝ) (hS : StrongWeakEq.Existence.Standing D f) (hR : StrongWeakEq.Existence.SecondOrderReg D f ft)
    (Qs : Matrix (Fin N) (Fin N) ℝ) (hW : StrongWeakEq.Existence.IsWeakEquilibrium D f Qs) :
    ((∀ i, ∀ Q ∈ StrongWeakEq.Existence.Controls D, Q ≠ Qs → StrongWeakEq.Existence.Gamma f Qs i (Qs i) = StrongWeakEq.Existence.Gamma f Qs i (Q i) →
        StrongWeakEq.Existence.Lambda f ft Qs i Q < StrongWeakEq.Existence.Lambda f ft Qs i Qs) → StrongWeakEq.Existence.IsStrongEquilibrium D f Qs) ∧
    ((∃ i, ∃ Q ∈ StrongWeakEq.Existence.Controls D, Q ≠ Qs ∧ StrongWeakEq.Existence.Gamma f Qs i (Qs i) = StrongWeakEq.Existence.Gamma f Qs i (Q i) ∧
        StrongWeakEq.Existence.Lambda f ft Qs i Qs < StrongWeakEq.Existence.Lambda f ft Qs i Q) → ¬ StrongWeakEq.Existence.IsStrongEquilibrium D f Qs) := by sorry

end StrongWeakEq.TwoState
