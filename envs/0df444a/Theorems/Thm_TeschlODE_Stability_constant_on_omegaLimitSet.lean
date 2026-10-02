-- Prove2me | Theorems.Thm_TeschlODE_Stability_constant_on_omegaLimitSet
-- name    : TeschlODE.Stability.constant_on_omegaLimitSet
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T13:45:27.77012+00:00
-- url     : https://prove2.me/theorems/087d9e7e-c188-4fe2-9889-dc4877637d29
-- title:
--   Theorem 6.15 — a function non-increasing along $\gamma_+(x) \subseteq U$ is constant on $\omega_+(x) \cap U$
-- statement:
--   Let $M \subseteq \mathbb{R}^n$ be open, $f \in C^1(M, \mathbb{R}^n)$, and $\Phi$ the flow with maximal intervals $I_x$. Let $U \subseteq M$ and let $L : U \to \mathbb{R}$ be continuous and bounded from below. If for some $x \in M$ we have $\gamma_+(x) \subseteq U$ and
--   $$L(\Phi(t_0, x)) \ge L(\Phi(t_1, x)), \qquad 0 < t_0 < t_1,\ t_0, t_1 \in I_x, \qquad (6.39)$$
--   then $L$ is constant on $\omega_+(x) \cap U$: $L(y) = L(z)$ for all $y, z \in \omega_+(x) \cap U$.
--
--   **Formalization Note.** (6.39) is required for the times of the forward orbit, $0 < t_0 < t_1 < T_+(x)$, where $\Phi(t, x) \in U$ and $L(\Phi(t,x))$ is defined; this is the weakest reading of "$t_0 < t_1$". $U \subseteq M$ is the book's implicit convention (the book writes only "$L : U \to \mathbb{R}$"). Bounded below is `BddBelow (L '' U)`.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 202, Theorem 6.15 and Eq. (6.39)

import Mathlib
import Definitions.Def_TeschlODE_Stability_IsIntegralCurve
import Definitions.Def_TeschlODE_Stability_IsMaximalFlow
import Definitions.Def_TeschlODE_Stability_semiOrbit
import Definitions.Def_TeschlODE_Stability_omegaLimitSet

namespace TeschlODE.Stability

theorem constant_on_omegaLimitSet {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (M : Set (EuclideanSpace ℝ (Fin n))) (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M)
    (I : EuclideanSpace ℝ (Fin n) → Set ℝ)
    (Φ : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hΦ : IsMaximalFlow f M I Φ)
    (U : Set (EuclideanSpace ℝ (Fin n))) (hUM : U ⊆ M)
    (L : EuclideanSpace ℝ (Fin n) → ℝ) (hL : ContinuousOn L U) (hLbdd : BddBelow (L '' U))
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ M) (horb : semiOrbit 1 I Φ x ⊆ U)
    (hmono : ∀ t₀ ∈ I x, ∀ t₁ ∈ I x, 0 < t₀ → t₀ < t₁ → L (Φ t₁ x) ≤ L (Φ t₀ x)) :
    ∀ y ∈ omegaLimitSet M 1 I Φ x ∩ U, ∀ z ∈ omegaLimitSet M 1 I Φ x ∩ U, L y = L z := by sorry

end TeschlODE.Stability
