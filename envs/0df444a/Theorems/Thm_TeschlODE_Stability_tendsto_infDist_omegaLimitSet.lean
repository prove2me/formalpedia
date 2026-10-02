-- Prove2me | Theorems.Thm_TeschlODE_Stability_tendsto_infDist_omegaLimitSet
-- name    : TeschlODE.Stability.tendsto_infDist_omegaLimitSet
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T13:37:03.333991+00:00
-- url     : https://prove2.me/theorems/dea7652b-739e-4426-8037-a8ad4a416cd1
-- title:
--   Lemma 6.7 — $d(\Phi(t,x), \omega_\sigma(x)) \to 0$ as $t \to \sigma\infty$
-- statement:
--   Let $M \subseteq \mathbb{R}^n$ be open, $f \in C^1(M, \mathbb{R}^n)$, and $\Phi$ the flow with maximal intervals $I_x$. Let $\sigma \in \{+1, -1\}$ and $x \in M$, and suppose $\gamma_\sigma(x)$ is contained in a compact set $C \subseteq M$. Then
--   $$\lim_{t \to \sigma\infty} d\big(\Phi(t, x), \omega_\sigma(x)\big) = 0, \qquad d(z, A) = \inf_{y \in A} |z - y| \quad (6.18).$$
--
--   **Formalization Note.** $t \to \sigma\infty$ is written as $\Phi(\sigma t, x)$ with $t \to +\infty$. $d(z, A)$ is Mathlib's `Metric.infDist`, which is $0$ for $A = \emptyset$; under the hypotheses $\omega_\sigma(x) \neq \emptyset$ (Lemma 6.6), so this convention never applies. $C \subseteq M$ as in Lemma 6.6; by Lemma 6.3, $\Phi(\sigma t, x)$ is defined for all $t > 0$.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 194, Lemma 6.7 and Eq. (6.18)

import Mathlib
import Definitions.Def_TeschlODE_Stability_IsIntegralCurve
import Definitions.Def_TeschlODE_Stability_IsMaximalFlow
import Definitions.Def_TeschlODE_Stability_semiOrbit
import Definitions.Def_TeschlODE_Stability_omegaLimitSet

namespace TeschlODE.Stability

theorem tendsto_infDist_omegaLimitSet {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (M : Set (EuclideanSpace ℝ (Fin n))) (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M)
    (I : EuclideanSpace ℝ (Fin n) → Set ℝ)
    (Φ : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hΦ : IsMaximalFlow f M I Φ)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ M)
    (C : Set (EuclideanSpace ℝ (Fin n))) (hC : IsCompact C) (hCM : C ⊆ M)
    (horb : semiOrbit σ I Φ x ⊆ C) :
    Filter.Tendsto (fun t : ℝ => Metric.infDist (Φ (σ * t) x) (omegaLimitSet M σ I Φ x))
      Filter.atTop (nhds 0) := by sorry

end TeschlODE.Stability
