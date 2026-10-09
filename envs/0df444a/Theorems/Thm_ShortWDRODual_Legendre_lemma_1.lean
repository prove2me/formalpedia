-- Prove2me | Theorems.Thm_ShortWDRODual_Legendre_lemma_1
-- name    : ShortWDRODual.Legendre.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:35:21.598991+00:00
-- url     : https://prove2.me/theorems/c2e7d7e1-0b67-4355-8781-4cbd25228ea1
-- title:
--   Lemma 1, p. 3 — 𝓛 is bounded below by 𝔼_ℙ̂[f], increasing and concave on [0, ∞)
-- statement:
--   Let $(\mathcal X,\mathcal F,\widehat{\mathbb P})$ be a probability space, $f:\mathcal X\to\mathbb R$ a measurable function with $\mathbb E_{\widehat{\mathbb P}}[f]>-\infty$, and $c:\mathcal X\times\mathcal X\to[0,\infty]$ a measurable transport cost with $c(x,x)=0$ for all $x$ (Assumption 1). Let $\mathcal L(\rho)$ be the worst-case loss over the Kantorovich ball of radius $\rho$. Then on $[0,\infty)$:
--
--   1. $\mathcal L(\rho)\ge\mathbb E_{\widehat{\mathbb P}}[f]$ for every $\rho\ge0$;
--   2. $\mathcal L$ is monotonically increasing;
--   3. $\mathcal L$ is concave: for $a,b\ge0$ and $t\in[0,1]$,
--   $$(1-t)\,\mathcal L(a)+t\,\mathcal L(b)\le\mathcal L\big((1-t)a+tb\big).$$
--
--   These properties of the worst-case loss are what allow the proof of Theorem 1 to apply one-dimensional convex duality to $-\mathcal L$.
--
--   **Formalization Note** $\mathcal L$ takes values in $(-\infty,+\infty]$ on $[0,\infty)$, so concavity is written as the inequality above in `EReal` with real weights; there Mathlib's $0\cdot\infty=0$ is the right convention (a convex combination with weight $0$), unlike the paper's $0\cdot\infty=\infty$ for $\lambda c$.
-- source:
--   Zhang, Yang & Gao, A Short and General Duality Proof for Wasserstein Distributionally Robust Optimization, arXiv:2205.00362v4, Lemma 1, p. 3 (PDF p. 3); proof in EC.1, p. ec1 (PDF p. 15)

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_ShortWDRODual_Legendre_Setting

namespace ShortWDRODual.Legendre

open MeasureTheory ModelRiskOT.Duality

theorem lemma_1 {X : Type*} [MeasurableSpace X]
    (Phat : Measure X) [IsProbabilityMeasure Phat]
    (f : X → ℝ) (c : X → X → ENNReal)
    (hf : Measurable f)
    (hfint : ⊥ < extIntegral Phat (fun x => (f x : EReal)))
    (hc : Measurable (fun p : X × X => c p.1 p.2))
    (hc0 : ∀ x, c x x = 0) :
    (∀ ρ : ℝ, 0 ≤ ρ →
      extIntegral Phat (fun x => (f x : EReal)) ≤ robustLoss c f Phat ρ) ∧
    MonotoneOn (robustLoss c f Phat) (Set.Ici 0) ∧
    (∀ a b t : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ t → t ≤ 1 →
      ((1 - t : ℝ) : EReal) * robustLoss c f Phat a +
          ((t : ℝ) : EReal) * robustLoss c f Phat b ≤
        robustLoss c f Phat ((1 - t) * a + t * b)) := by sorry

end ShortWDRODual.Legendre
