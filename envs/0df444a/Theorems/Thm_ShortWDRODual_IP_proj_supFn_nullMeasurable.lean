-- Prove2me | Theorems.Thm_ShortWDRODual_IP_proj_supFn_nullMeasurable
-- name    : ShortWDRODual.IP.proj_supFn_nullMeasurable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:31:41.894509+00:00
-- url     : https://prove2.me/theorems/edc9a841-e1b8-4a0c-83ca-da4f2b8275c6
-- title:
--   Proof of Proposition 1, p. ec2 — under (Proj), Φ(x̂) = sup_x φ(x̂, x) is ℙ̂-measurable
-- statement:
--   Let $(\mathcal X,\mathcal F,\widehat{\mathbb P})$ be a probability space satisfying the measurable projection condition (Proj), and let $\phi:\mathcal X\times\mathcal X\to\mathbb R\cup\{-\infty\}$ be an $(\mathcal F\otimes\mathcal F)$-measurable diagonally dominant function. Then
--
--   $$\Phi(\widehat x)=\sup_{x\in\mathcal X}\phi(\widehat x,x)\quad\text{is }\widehat{\mathbb P}\text{-measurable},$$
--
--   i.e. measurable with respect to the completion $\mathcal F_{\widehat{\mathbb P}}$.
--
--   This is the first half of the sufficiency direction of Proposition 1: it supplies the measurability clause of (IP), so that only the equality of expectations remains.
--
--   **Formalization Note** $\widehat{\mathbb P}$-measurability is `NullMeasurable (supFn φ) Phat`.
-- source:
--   Zhang, Yang & Gao, A Short and General Duality Proof for Wasserstein Distributionally Robust Optimization, arXiv:2205.00362v4, proof of Proposition 1 (sufficiency, first paragraph), p. ec2 (PDF p. 16), "Therefore, Φ is ℙ̂-measurable"

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_ShortWDRODual_IP_Setting

namespace ShortWDRODual.IP

open MeasureTheory ModelRiskOT.Duality
open scoped ENNReal

theorem proj_supFn_nullMeasurable {X : Type*} [MeasurableSpace X] (Phat : Measure X)
    [IsProbabilityMeasure Phat] (hProj : Proj Phat) (φ : X × X → EReal) (hφ : DiagDomFun φ)
    (hφtop : ∀ p, φ p ≠ ⊤) :
    NullMeasurable (ShortWDRODual.Legendre.supFn φ) Phat := by sorry

end ShortWDRODual.IP
