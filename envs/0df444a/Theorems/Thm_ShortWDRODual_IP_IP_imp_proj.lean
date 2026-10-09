-- Prove2me | Theorems.Thm_ShortWDRODual_IP_IP_imp_proj
-- name    : ShortWDRODual.IP.IP_imp_proj
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:31:23.726597+00:00
-- url     : https://prove2.me/theorems/4e94b58f-e210-4b3b-8c38-b1e25f4eb3d5
-- title:
--   Proof of Proposition 1, p. ec3 — (IP) for all diagonally dominant φ implies (Proj)
-- statement:
--   Let $(\mathcal X,\mathcal F,\widehat{\mathbb P})$ be a probability space such that every $(\mathcal F\otimes\mathcal F)$-measurable diagonally dominant function $\phi:\mathcal X\times\mathcal X\to\mathbb R\cup\{-\infty\}$ satisfies the interchangeability principle (IP). Then the measurable projection condition holds: for every diagonally dominant set $A\in\mathcal F\otimes\mathcal F$,
--
--   $$\mathrm{Proj}_{\widehat x}(A)=\{\widehat x\in\mathcal X:(\widehat x,x)\in A\text{ for some }x\in\mathcal X\}\in\mathcal F_{\widehat{\mathbb P}}.$$
--
--   This is the first half of the necessity direction of Proposition 1.
--
--   **Formalization Note** "$\in\mathcal F_{\widehat{\mathbb P}}$" is `NullMeasurableSet (Prod.fst '' A) Phat`.
-- source:
--   Zhang, Yang & Gao, A Short and General Duality Proof for Wasserstein Distributionally Robust Optimization, arXiv:2205.00362v4, proof of Proposition 1 (necessity), p. ec3 (PDF p. 17), "Therefore (IP) implies (Proj)"

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_ShortWDRODual_IP_Setting

namespace ShortWDRODual.IP

open MeasureTheory ModelRiskOT.Duality
open scoped ENNReal

theorem IP_imp_proj {X : Type*} [MeasurableSpace X] (Phat : Measure X)
    [IsProbabilityMeasure Phat]
    (hIP : ∀ φ : X × X → EReal, DiagDomFun φ → (∀ p, φ p ≠ ⊤) → ShortWDRODual.Legendre.IP Phat φ) :
    Proj Phat := by sorry

end ShortWDRODual.IP
