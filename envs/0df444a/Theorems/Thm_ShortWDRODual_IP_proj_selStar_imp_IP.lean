-- Prove2me | Theorems.Thm_ShortWDRODual_IP_proj_selStar_imp_IP
-- name    : ShortWDRODual.IP.proj_selStar_imp_IP
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:31:11.183147+00:00
-- url     : https://prove2.me/theorems/c0f12c00-4409-4fc7-a043-94b2ecd1e11a
-- title:
--   Proof of Proposition 1, pp. ec2–ec3 — (Proj) and (Sel*) imply (IP) for all diagonally dominant φ
-- statement:
--   Let $(\mathcal X,\mathcal F,\widehat{\mathbb P})$ be a probability space satisfying the measurable projection condition (Proj) and the weak measurable selection condition (Sel\*). Then every $(\mathcal F\otimes\mathcal F)$-measurable diagonally dominant function $\phi:\mathcal X\times\mathcal X\to\mathbb R\cup\{-\infty\}$ satisfies the interchangeability principle: $\Phi(\widehat x)=\sup_x\phi(\widehat x,x)$ is $\widehat{\mathbb P}$-measurable and
--
--   $$\mathbb E_{\widehat X\sim\widehat{\mathbb P}}\Big[\sup_{x\in\mathcal X}\phi(\widehat X,x)\Big]=\sup_{\gamma\in\Gamma_{\widehat{\mathbb P}}}\mathbb E_{(\widehat X,X)\sim\gamma}\big[\phi(\widehat X,X)\big].$$
--
--   This is the sufficiency direction of Proposition 1. The case $\mathbb E_{\widehat{\mathbb P}}[\Phi]=+\infty$ is included.
--
--   **Formalization Note** Expectations are `extIntegral` values; $\infty-\infty$ is read as $-\infty$.
-- source:
--   Zhang, Yang & Gao, A Short and General Duality Proof for Wasserstein Distributionally Robust Optimization, arXiv:2205.00362v4, proof of Proposition 1 (sufficiency), pp. ec2–ec3 (PDF pp. 16–17), "This proves that (Proj) and (Sel*) combined imply (IP) holds for all diagonally dominant functions"

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_ShortWDRODual_IP_Setting

namespace ShortWDRODual.IP

open MeasureTheory ModelRiskOT.Duality
open scoped ENNReal

theorem proj_selStar_imp_IP {X : Type*} [MeasurableSpace X] (Phat : Measure X)
    [IsProbabilityMeasure Phat] (hProj : Proj Phat) (hSel : SelStar Phat) :
    ∀ φ : X × X → EReal, DiagDomFun φ → (∀ p, φ p ≠ ⊤) → ShortWDRODual.Legendre.IP Phat φ := by sorry

end ShortWDRODual.IP
