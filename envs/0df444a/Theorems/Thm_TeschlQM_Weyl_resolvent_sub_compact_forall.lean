-- Prove2me | Theorems.Thm_TeschlQM_Weyl_resolvent_sub_compact_forall
-- name    : TeschlQM.Weyl.resolvent_sub_compact_forall
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T23:25:25.144311+00:00
-- url     : https://prove2.me/theorems/25d849ea-a6e3-46a5-aa6c-02c5ba3d94e1
-- title:
--   Lemma 6.21 (first part) — compactness of R_A(z) − R_B(z) at one z gives it at all z
-- statement:
--   Let $A$ and $B$ be linear operators in a complex Hilbert space $\mathfrak H$. Suppose
--   $$R_A(z) - R_B(z) \in \mathfrak C(\mathfrak H)$$
--   for one $z \in \rho(A) \cap \rho(B)$. Then $R_A(z') - R_B(z') \in \mathfrak C(\mathfrak H)$ for all $z' \in \rho(A) \cap \rho(B)$.
--
--   This shows that the hypothesis of Weyl's theorem does not depend on the chosen spectral parameter.
--
--   **Formalization Note.** "For one $z$" is an existential over $z$ together with the resolvents $R_A(z)$, $R_B(z)$ (`IsResolventAt`); the conclusion quantifies over every $z'$ and every pair of resolvents at $z'$ (which are unique). Compactness is Mathlib's `IsCompactOperator`. Only the first part of the book's Lemma 6.21 is stated; the second part, $f(A) - f(B) \in \mathfrak C(\mathfrak H)$ for $f \in C_\infty(\mathbb R)$, needs the functional calculus and is not part of this item.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 147, Lemma 6.21

import Mathlib
import Definitions.Def_TeschlQM_Shared_resolventSet

namespace TeschlQM.Weyl

/-- Teschl, Lemma 6.21 (first part), p. 147. Suppose `R_A(z) - R_B(z) ∈ ℭ(ℌ)` (6.35) for one
`z ∈ ρ(A) ∩ ρ(B)`. Then this holds for all `z ∈ ρ(A) ∩ ρ(B)`. The second part of the lemma,
`f(A) - f(B) ∈ ℭ(ℌ)` for `f ∈ C_∞(ℝ)`, needs the functional calculus and is not stated here. -/
theorem resolvent_sub_compact_forall {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A B : H →ₗ.[ℂ] H)
    (h : ∃ (z : ℂ) (RA RB : H →L[ℂ] H), TeschlQM.Shared.IsResolventAt A z RA ∧ TeschlQM.Shared.IsResolventAt B z RB ∧
      IsCompactOperator (RA - RB)) :
    ∀ (z : ℂ) (RA RB : H →L[ℂ] H), TeschlQM.Shared.IsResolventAt A z RA → TeschlQM.Shared.IsResolventAt B z RB →
      IsCompactOperator (RA - RB) := by sorry

end TeschlQM.Weyl
