-- Prove2me | Theorems.Thm_ShortWDRODual_Legendre_lemma_2_conj
-- name    : ShortWDRODual.Legendre.lemma_2_conj
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:35:42.912089+00:00
-- url     : https://prove2.me/theorems/1d287cbd-6795-4bf1-a035-f12ce111a886
-- title:
--   Lemma 2 (first half), p. 13 — λ ↦ (−𝓛)*(−λ) is ≥ 𝔼_ℙ̂[f], decreasing, convex and lsc on [0, ∞)
-- statement:
--   Assume Assumption 1 (as in Lemma 1), and write $F(\lambda)=(-\mathcal L)^*(-\lambda)$, which for $\lambda\ge0$ is the value of (P-soft). Then on $[0,\infty)$:
--
--   1. $F(\lambda)\ge\mathbb E_{\widehat{\mathbb P}}[f]$ for every $\lambda\ge0$;
--   2. $F$ is monotonically decreasing;
--   3. $F$ is convex: for $a,b\ge0$ and $t\in[0,1]$,
--   $$F\big((1-t)a+tb\big)\le(1-t)F(a)+tF(b);$$
--   4. $F$ is lower semi-continuous on $[0,\infty)$ (relative to $[0,\infty)$).
--
--   In the proof of Theorem 1 these properties let the infimum over $\lambda\ge0$ be attained and give right continuity at $\lambda=0$.
--
--   **Formalization Note** Lower semi-continuity is `LowerSemicontinuousOn` on $[0,\infty)$, i.e. relative to that set, which is what the paper's "on $[0,\infty)$" asserts. Convexity is written with real weights in `EReal`.
-- source:
--   Zhang, Yang & Gao, A Short and General Duality Proof for Wasserstein Distributionally Robust Optimization, arXiv:2205.00362v4, Lemma 2, p. 13 (PDF p. 13), statement for (−𝓛)*(−·); proof p. ec2 (PDF p. 16)

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_ShortWDRODual_Legendre_Setting

namespace ShortWDRODual.Legendre

open MeasureTheory ModelRiskOT.Duality

theorem lemma_2_conj {X : Type*} [MeasurableSpace X]
    (Phat : Measure X) [IsProbabilityMeasure Phat]
    (f : X → ℝ) (c : X → X → ENNReal)
    (hf : Measurable f)
    (hfint : ⊥ < extIntegral Phat (fun x => (f x : EReal)))
    (hc : Measurable (fun p : X × X => c p.1 p.2))
    (hc0 : ∀ x, c x x = 0) :
    let F : ℝ → EReal := fun lam => legendre (fun ρ => - robustLoss c f Phat ρ) (-lam)
    (∀ lam : ℝ, 0 ≤ lam → extIntegral Phat (fun x => (f x : EReal)) ≤ F lam) ∧
    AntitoneOn F (Set.Ici 0) ∧
    (∀ a b t : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ t → t ≤ 1 →
      F ((1 - t) * a + t * b) ≤ ((1 - t : ℝ) : EReal) * F a + ((t : ℝ) : EReal) * F b) ∧
    LowerSemicontinuousOn F (Set.Ici 0) := by sorry

end ShortWDRODual.Legendre
