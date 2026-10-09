-- Prove2me | Theorems.Thm_ShortWDRODual_Legendre_lemma_2_G
-- name    : ShortWDRODual.Legendre.lemma_2_G
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:35:32.255996+00:00
-- url     : https://prove2.me/theorems/5fa479d8-d2dd-4809-9644-3ae6c680d678
-- title:
--   Lemma 2 (second half), p. 13 — 𝒢(λ) = 𝔼_ℙ̂[sup_x f(x) − λc(X̂, x)] is ≥ 𝔼_ℙ̂[f], decreasing, convex and lsc on [0, ∞)
-- statement:
--   Assume Assumption 1 (as in Lemma 1), and let
--   $$\mathcal G(\lambda)=\mathbb E_{\widehat X\sim\widehat{\mathbb P}}\Big[\sup_{x\in\mathcal X}\{f(x)-\lambda c(\widehat X,x)\}\Big],\qquad\lambda\ge0,$$
--   with the convention $0\cdot\infty=\infty$. Suppose that for every $\lambda>0$ the function $\widehat x\mapsto\sup_{x}\{f(x)-\lambda c(\widehat x,x)\}$ is $\widehat{\mathbb P}$-measurable. Then on $[0,\infty)$:
--
--   1. $\mathcal G(\lambda)\ge\mathbb E_{\widehat{\mathbb P}}[f]$ for every $\lambda\ge0$;
--   2. $\mathcal G$ is monotonically decreasing;
--   3. $\mathcal G$ is convex: for $a,b\ge0$ and $t\in[0,1]$, $\mathcal G((1-t)a+tb)\le(1-t)\mathcal G(a)+t\,\mathcal G(b)$;
--   4. $\mathcal G$ is lower semi-continuous on $[0,\infty)$.
--
--   In the proof of Theorem 1 these properties make the minimum over $\lambda\ge0$ in (D) attained.
--
--   **Formalization Note** The measurability hypothesis is the presupposition of the paper's definition of $\mathcal G(\lambda)$ as an expectation (§2.1 allows expectations only of measurable functions); without it the expectation is a lower integral, which is only superadditive and for which the convexity step fails. It is assumed only for $\lambda>0$: at $\lambda=0$ the integrand is the increasing limit of the integrands at $\lambda=1/n$. Lower semi-continuity is relative to $[0,\infty)$.
-- source:
--   Zhang, Yang & Gao, A Short and General Duality Proof for Wasserstein Distributionally Robust Optimization, arXiv:2205.00362v4, Lemma 2, p. 13 (PDF p. 13), statement for 𝒢(·); proof p. ec2 (PDF p. 16)

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_ShortWDRODual_Legendre_Setting

namespace ShortWDRODual.Legendre

open MeasureTheory ModelRiskOT.Duality

theorem lemma_2_G {X : Type*} [MeasurableSpace X]
    (Phat : Measure X) [IsProbabilityMeasure Phat]
    (f : X → ℝ) (c : X → X → ENNReal)
    (hf : Measurable f)
    (hfint : ⊥ < extIntegral Phat (fun x => (f x : EReal)))
    (hc : Measurable (fun p : X × X => c p.1 p.2))
    (hc0 : ∀ x, c x x = 0)
    (hG : ∀ lam : ℝ, 0 < lam → NullMeasurable (supFn (phiLam c f lam)) Phat) :
    (∀ lam : ℝ, 0 ≤ lam → extIntegral Phat (fun x => (f x : EReal)) ≤ dualG c f Phat lam) ∧
    AntitoneOn (dualG c f Phat) (Set.Ici 0) ∧
    (∀ a b t : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ t → t ≤ 1 →
      dualG c f Phat ((1 - t) * a + t * b) ≤
        ((1 - t : ℝ) : EReal) * dualG c f Phat a + ((t : ℝ) : EReal) * dualG c f Phat b) ∧
    LowerSemicontinuousOn (dualG c f Phat) (Set.Ici 0) := by sorry

end ShortWDRODual.Legendre
