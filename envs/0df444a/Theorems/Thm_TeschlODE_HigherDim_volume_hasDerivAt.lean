-- Prove2me | Theorems.Thm_TeschlODE_HigherDim_volume_hasDerivAt
-- name    : TeschlODE.HigherDim.volume_hasDerivAt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T16:28:44.242596+00:00
-- url     : https://prove2.me/theorems/b78c4c68-3160-4ec0-ad33-11b0097c60b1
-- title:
--   Lemma 8.8 — Liouville's formula for volumes, $\dot V(t) = \int_{U(t)} \operatorname{div} f\,dx$ (8.28)
-- statement:
--   Let $f : \mathbb{R}^n \to \mathbb{R}^n$ be $C^1$ and let $\Phi$ be the (local) flow of the dynamical system $\dot x = f(x)$ on $\mathbb{R}^n$. Let $U$ be a bounded open subset of $\mathbb{R}^n$, write $U(t) = \Phi(t, U)$ and $V(t) = |U(t)| = \int_{U(t)} dx$ (Lebesgue measure). Let $t_0$ be a time at which every point of the closure $\overline U$ is still alive, $t_0 \in I_x$ for all $x \in \overline U$. Then $V(t_0) < \infty$, $\operatorname{div} f$ is integrable on $U(t_0)$, and $V$ is differentiable at $t_0$ with
--   $$\dot V(t_0) = \int_{U(t_0)} \operatorname{div}(f(x))\,dx. \qquad (8.28)$$
--
--   This is the book's generalization of Liouville's formula (3.91) from linear systems to volumes transported by a nonlinear flow. It gives $V(t) = V e^{-(1+\sigma+b)t}$ for the Lorenz equation and, since a Hamiltonian vector field has zero divergence, Liouville's theorem 8.10.
--
--   **Formalization Note.** The book states the lemma for "a dynamical system on $\mathbb{R}^n$" under the chapter's standing assumption that the flow is complete, so that $U(t)$ is defined for all $t$. The statement keeps the local flow and requires instead that $\overline U$ be alive at $t_0$; this is implied by completeness, and it is needed: if only the points of $U$ are alive, $U(t_0)$ can have infinite volume (for $\dot x = x^2$, $U = (0, 1)$, $t_0 = 1$). $f \in C^1$ is the book's standing regularity (Chapter 6) and what the first variational equation in the proof needs. The two finiteness/integrability conjuncts rule out the junk values of `ENNReal.toReal` and of the Bochner integral. $V$ is read as the real number $(\text{volume}(\Phi(t, U)))$`.toReal`, which is finite for $t$ near $t_0$.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 236, Lemma 8.8, Eq. (8.28)

import Mathlib
import Definitions.Def_TeschlODE_HigherDim_IsIntegralCurve
import Definitions.Def_TeschlODE_HigherDim_IsMaximalFlow
import Definitions.Def_TeschlODE_HigherDim_divergence

open MeasureTheory

namespace TeschlODE.HigherDim

/-- Teschl, Lemma 8.8, p. 236, (8.28): for a `C¹` vector field on `ℝⁿ` with flow `Φ`, a bounded
open `U` and a time `t₀` at which every point of the closure `Ū` is still alive, the volume
`V(t) = |Φ(t, U)|` is finite at `t₀`, `div f` is integrable on `U(t₀) = Φ(t₀, U)`, and
`V̇(t₀) = ∫_{U(t₀)} div f(x) dx`. -/
theorem volume_hasDerivAt {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hf : ContDiff ℝ 1 f)
    (I : EuclideanSpace ℝ (Fin n) → Set ℝ)
    (Φ : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hΦ : IsMaximalFlow f Set.univ I Φ)
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (t₀ : ℝ) (ht₀ : ∀ x ∈ closure U, t₀ ∈ I x) :
    volume (Φ t₀ '' U) < ⊤ ∧ IntegrableOn (divergence f) (Φ t₀ '' U) ∧
      HasDerivAt (fun t : ℝ => (volume (Φ t '' U)).toReal)
        (∫ x in Φ t₀ '' U, divergence f x) t₀ := by sorry

end TeschlODE.HigherDim
