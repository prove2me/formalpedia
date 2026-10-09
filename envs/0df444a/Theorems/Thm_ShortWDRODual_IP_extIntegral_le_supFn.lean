-- Prove2me | Theorems.Thm_ShortWDRODual_IP_extIntegral_le_supFn
-- name    : ShortWDRODual.IP.extIntegral_le_supFn
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:31:20.099863+00:00
-- url     : https://prove2.me/theorems/ab96275a-8861-43dd-b4b2-bfdbebc483da
-- title:
--   Proof of Proposition 1, p. ec3 — E_ℙ̂[Φ(X̂)] ≥ E_γ[φ(X̂, X)] for every γ ∈ Γ_ℙ̂
-- statement:
--   Let $(\mathcal X,\mathcal F,\widehat{\mathbb P})$ be a probability space and $\phi:\mathcal X\times\mathcal X\to\mathbb R\cup\{-\infty\}$ an $(\mathcal F\otimes\mathcal F)$-measurable function whose pointwise supremum $\Phi(\widehat x)=\sup_{x\in\mathcal X}\phi(\widehat x,x)$ is $\widehat{\mathbb P}$-measurable. Then for every probability measure $\gamma$ on $\mathcal X\times\mathcal X$ with first marginal $\widehat{\mathbb P}$,
--
--   $$\mathbb E_{\widehat X\sim\widehat{\mathbb P}}\big[\Phi(\widehat X)\big]\ \ge\ \mathbb E_{(\widehat X,X)\sim\gamma}\big[\phi(\widehat X,X)\big].$$
--
--   This is the easy inequality "$\ge$" in (IP), which the paper derives from $\phi(\widehat x,x)\le\Phi(\widehat x)$.
--
--   **Formalization Note** Both expectations are `extIntegral` values in $[-\infty,\infty]$ ($\int\varphi^+-\int\varphi^-$, with $\infty-\infty$ read as $-\infty$). In the paper, $\phi$ is moreover diagonally dominant at this point and $\Phi$ is $\widehat{\mathbb P}$-measurable by the preceding step; diagonal dominance is not used by the inequality and is not assumed here, which makes the statement slightly more general.
-- source:
--   Zhang, Yang & Gao, A Short and General Duality Proof for Wasserstein Distributionally Robust Optimization, arXiv:2205.00362v4, proof of Proposition 1, first display, p. ec3 (PDF p. 17)

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_ShortWDRODual_IP_Setting

namespace ShortWDRODual.IP

open MeasureTheory ModelRiskOT.Duality
open scoped ENNReal

theorem extIntegral_le_supFn {X : Type*} [MeasurableSpace X] (Phat : Measure X)
    [IsProbabilityMeasure Phat] (φ : X × X → EReal) (hφ : Measurable φ) (hφtop : ∀ p, φ p ≠ ⊤)
    (hΦ : NullMeasurable (ShortWDRODual.Legendre.supFn φ) Phat) (γ : Measure (X × X)) (hγ : γ ∈ ShortWDRODual.Legendre.couplingsFst Phat) :
    extIntegral γ φ ≤ extIntegral Phat (ShortWDRODual.Legendre.supFn φ) := by sorry

end ShortWDRODual.IP
