-- Prove2me | Theorems.Thm_RamadgeWonham_Quotient_thm_10_1_reduction
-- name    : RamadgeWonham.Quotient.thm_10_1_reduction
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:47:15.717484+00:00
-- url     : https://prove2.me/theorems/52c1b60b-aa46-4a23-b98b-90aac8ee8e11
-- title:
--   Proof of Theorem 10.1, p. 223 — L(𝒮⁰/𝒢) = K₃ follows from enablement conditions (i), (ii)
-- statement:
--   Let $\mathcal G$ be a trim generator over a finite alphabet $\Sigma$ with controllable events $\Sigma_c$, and let $K_3 \subseteq L(\mathcal G)$ be nonempty and closed. Let $\hat S^0 = (X^0, \Sigma, \xi^0, x^0_0, X^0)$ be a trim recognizer for $K_3$ in which every state is marked, and let $\mathcal S^0 = (S^0, \phi^0)$ with $S^0 = (X^0, \Sigma, \xi^0, x^0_0, X^0_m)$ for some $X^0_m \subseteq X^0$ and $\phi^0 : X^0 \to \{0,1\}^{\Sigma_c}$. Suppose that for all $\sigma \in \Sigma$ and $x^0 \in X^0$:
--
--   1. if some $s$ has $\xi^0(s, x^0_0) = x^0$, $s\sigma \in L(\mathcal G)$ and $s\sigma \notin K_3$, then $\phi^0(x^0)(\sigma) = 0$;
--   2. if some $s$ has $\xi^0(s, x^0_0) = x^0$ and $s\sigma \in K_3$, then $\phi^0(x^0)(\sigma) = 1$.
--
--   Then
--   $$L(\mathcal S^0/\mathcal G) = K_3.$$
--
--   **Formalization Note** $\phi^0(x^0)(\sigma) = 0$ is rendered as "$\sigma$ is not enabled at $x^0$", i.e. $\sigma \in \Sigma_c$ and $\phi^0(x^0)(\sigma) = 0$ (uncontrollable events are always enabled, p. 210). The page's "$(\forall \sigma, x^0)(\exists s)\, A \Rightarrow B$" is read as $\forall \sigma, x^0: (\exists s,\ A) \Rightarrow B$, the form the proof uses.
-- source:
--   Ramadge and Wonham, Supervisory Control of a Class of Discrete Event Processes, SIAM J. Control Optim. 25(1), 1987, p. 223, proof of Theorem 10.1, fourth paragraph, conditions (i), (ii) (by the argument of the proof of Proposition 5.1, p. 215)

import Mathlib
import Definitions.Def_RamadgeWonham_Quotient_Reduced
import Definitions.Def_RamadgeWonham_Quotient_Recognizer

namespace RamadgeWonham.Quotient

open Shared.Generator

/-- Proof of Theorem 10.1 (p. 223, fourth paragraph), "by the argument used in the proof of
Proposition 5.1": let `K₃ ⊆ L(𝒢)` be nonempty and closed, let `Ŝ⁰ = (X⁰, Σ, ξ⁰, x⁰₀, X⁰)` be a trim
recognizer for `K₃`, and let `𝒮⁰ = (S⁰, φ⁰)` with `S⁰ = (X⁰, Σ, ξ⁰, x⁰₀, X⁰_m)`. If
(i) `(∀σ, x⁰)(∃s) ξ⁰(s, x⁰₀) = x⁰ and sσ ∈ L(𝒢) and sσ ∉ K₃ ⇒ φ⁰(x⁰)(σ) = 0`, and
(ii) `(∀σ, x⁰)(∃s) ξ⁰(s, x⁰₀) = x⁰ and sσ ∈ K₃ ⇒ φ⁰(x⁰)(σ) = 1`, then `L(𝒮⁰/𝒢) = K₃`. -/
theorem thm_10_1_reduction
    {α : Type} [Fintype α] {Ec : Set α} (𝒢 : Shared.Generator α) (h𝒢 : 𝒢.L = Shared.pre 𝒢.Lm)
    (K3 : Set (List α)) (hK3ne : K3.Nonempty) (hK3cl : Shared.pre K3 = K3) (hK3G : K3 ⊆ 𝒢.L)
    (R : Shared.Generator α) (hRrec : IsRecognizer R K3) (hRtrim : R.IsTrim) (hRQm : R.Qm = Set.univ)
    (Xm0 : Set R.Q) (φ0 : R.Q → Ec → Bool)
    (hi : ∀ (σ : α) (x0 : R.Q), (∃ s : List α, R.run s = some x0 ∧ s ++ [σ] ∈ 𝒢.L ∧
        s ++ [σ] ∉ K3) → ¬ (ofRecognizer R Xm0 φ0).enabled x0 σ)
    (hii : ∀ (σ : α) (x0 : R.Q), (∃ s : List α, R.run s = some x0 ∧ s ++ [σ] ∈ K3) →
        (ofRecognizer R Xm0 φ0).enabled x0 σ) :
    Shared.Lsup 𝒢 (ofRecognizer R Xm0 φ0) = K3 := by sorry

end RamadgeWonham.Quotient
