-- Prove2me | Theorems.Thm_RamadgeWonham_Quotient_quotient_structure_theorem
-- name    : RamadgeWonham.Quotient.quotient_structure_theorem
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:49:09.258989+00:00
-- url     : https://prove2.me/theorems/aed92d61-0d00-46fd-8c41-eb18234ff348
-- title:
--   Theorem 10.1, p. 223 — quotient structure theorem: a reduced, trim supervisor is a projection of one built on a recognizer
-- statement:
--   Let $\mathcal G = (Q, \Sigma, \delta, q_0, Q_m)$ be a trim generator over a finite alphabet $\Sigma$ with controllable events $\Sigma_c$. Let $\mathcal S = (S, \phi)$, $S = (X, \Sigma, \xi, x_0, X_m)$, be a complete supervisor for $\mathcal G$ with $S$ accessible. Write
--   $$K_1 := L_m(\mathcal S/\mathcal G), \qquad K_3 := L(\mathcal S/\mathcal G),$$
--   and assume that $S$ is $K_3$-reduced and $K_3$-trim. Let $\hat S^0 = (X^0, \Sigma, \xi^0, x^0_0, X^0)$ be a trim recognizer for $K_3$ (all of its states marked). Then there exist a subset $X^0_m \subseteq X^0$ and a state feedback map $\phi^0 : X^0 \to \{0,1\}^{\Sigma_c}$ such that, with
--   $$\mathcal S^0 := (S^0, \phi^0), \qquad S^0 := (X^0, \Sigma, \xi^0, x^0_0, X^0_m),$$
--
--   1. $\mathcal S^0$ is a complete supervisor for $\mathcal G$ with $L_m(\mathcal S^0/\mathcal G) = K_1$ and $L(\mathcal S^0/\mathcal G) = K_3$;
--   2. there is a projection $\pi : \mathcal S^0 \to \mathcal S$;
--   3. if $\mathcal S$ is proper, then so is $\mathcal S^0$.
--
--   In words: every supervisor with these reduction properties, such as the efficient supervisor of §9, is a quotient (lumped model) of a supervisor whose automaton is a recognizer of the desired closed-loop behaviour.
--
--   **Formalization Note** The standing assumptions are hypotheses: $\Sigma$ finite, $\mathcal G$ trim ($L(\mathcal G) = \bar L_m(\mathcal G)$), $S$ accessible. $\mathcal S^0$ is built on the *given* recognizer $\hat S^0$. The paper's $\phi^0 : X^0 \to \{0,1\}^\Sigma$ is encoded as a map into $\{0,1\}^{\Sigma_c}$, which is the same object under the convention that uncontrollable events are always enabled (p. 210).
-- source:
--   Ramadge and Wonham, Supervisory Control of a Class of Discrete Event Processes, SIAM J. Control Optim. 25(1), 1987, p. 222, §10 hypotheses; p. 223, Theorem 10.1 (i)-(iii); proof pp. 223-224

import Mathlib
import Definitions.Def_RamadgeWonham_Quotient_Projection
import Definitions.Def_RamadgeWonham_Quotient_Reduced
import Definitions.Def_RamadgeWonham_Quotient_Recognizer

namespace RamadgeWonham.Quotient

open Shared.Generator

/-- Theorem 10.1 (quotient structure theorem, p. 223). Let `𝒮 = (S, φ)` be an accessible complete
supervisor for the trim generator `𝒢`, write `K₁ := L_m(𝒮/𝒢)`, `K₃ := L(𝒮/𝒢)`, assume `S` is
`K₃`-reduced and `K₃`-trim, and let `Ŝ⁰ = (X⁰, Σ, ξ⁰, x⁰₀, X⁰)` be a trim recognizer for `K₃`. Then
there exist `X⁰_m ⊆ X⁰` and `φ⁰ : X⁰ → {0,1}^Σ` such that (i) `𝒮⁰ := (S⁰, φ⁰)`,
`S⁰ := (X⁰, Σ, ξ⁰, x⁰₀, X⁰_m)`, is a complete supervisor for `𝒢` with `L_m(𝒮⁰/𝒢) = K₁` and
`L(𝒮⁰/𝒢) = K₃`; (ii) there is a projection `π : 𝒮⁰ → 𝒮`; (iii) if `𝒮` is proper then so is
`𝒮⁰`. -/
theorem quotient_structure_theorem
    {α : Type} [Fintype α] {Ec : Set α} (𝒢 : Shared.Generator α) (h𝒢 : 𝒢.L = Shared.pre 𝒢.Lm)
    (𝒮 : Shared.Supervisor α Ec) (h𝒮acc : 𝒮.S.Accessible) (h𝒮 : Shared.Complete 𝒢 𝒮)
    (hred : KReduced 𝒮.S (Shared.Lsup 𝒢 𝒮)) (htrim : KTrim 𝒮.S (Shared.Lsup 𝒢 𝒮))
    (R : Shared.Generator α) (hRrec : IsRecognizer R (Shared.Lsup 𝒢 𝒮)) (hRtrim : R.IsTrim)
    (hRQm : R.Qm = Set.univ) :
    ∃ (Xm0 : Set R.Q) (φ0 : R.Q → Ec → Bool),
      Shared.Complete 𝒢 (ofRecognizer R Xm0 φ0) ∧
      Shared.Lmsup 𝒢 (ofRecognizer R Xm0 φ0) = Shared.Lmsup 𝒢 𝒮 ∧
      Shared.Lsup 𝒢 (ofRecognizer R Xm0 φ0) = Shared.Lsup 𝒢 𝒮 ∧
      (∃ π : R.Q → 𝒮.S.Q, IsProjection (ofRecognizer R Xm0 φ0) 𝒮 π) ∧
      (Shared.Proper 𝒢 𝒮 → Shared.Proper 𝒢 (ofRecognizer R Xm0 φ0)) := by sorry

end RamadgeWonham.Quotient
