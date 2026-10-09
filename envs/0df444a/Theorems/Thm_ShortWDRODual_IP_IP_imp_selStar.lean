-- Prove2me | Theorems.Thm_ShortWDRODual_IP_IP_imp_selStar
-- name    : ShortWDRODual.IP.IP_imp_selStar
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:31:24.384393+00:00
-- url     : https://prove2.me/theorems/628d62b3-aa0a-48c9-850b-183df29b602d
-- title:
--   Proof of Proposition 1, pp. ec3–ec4 — (IP) for all diagonally dominant φ implies (Sel*)
-- statement:
--   Let $(\mathcal X,\mathcal F,\widehat{\mathbb P})$ be a probability space such that every $(\mathcal F\otimes\mathcal F)$-measurable diagonally dominant function $\phi:\mathcal X\times\mathcal X\to\mathbb R\cup\{-\infty\}$ satisfies the interchangeability principle (IP). Then the weak measurable selection condition holds: for every diagonally dominant set-valued function $E:\mathcal X\to\mathcal F\setminus\{\emptyset\}$ with $\mathrm{Graph}(E)\in\mathcal F\otimes\mathcal F$ there is $\gamma\in\Gamma_{\widehat{\mathbb P}}$ with
--
--   $$\operatorname{supp}\gamma\subset\mathrm{Graph}(E).$$
--
--   This is the second half of the necessity direction of Proposition 1.
--
--   **Formalization Note** $\operatorname{supp}\gamma\subset\mathrm{Graph}(E)$ is read as $\gamma(\mathrm{Graph}(E)^c)=0$, since $\mathcal X$ carries no topology.
-- source:
--   Zhang, Yang & Gao, A Short and General Duality Proof for Wasserstein Distributionally Robust Optimization, arXiv:2205.00362v4, proof of Proposition 1 (necessity), pp. ec3–ec4 (PDF pp. 17–18), "Therefore (IP) implies (Sel*)"

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_ShortWDRODual_IP_Setting

namespace ShortWDRODual.IP

open MeasureTheory ModelRiskOT.Duality
open scoped ENNReal

theorem IP_imp_selStar {X : Type*} [MeasurableSpace X] (Phat : Measure X)
    [IsProbabilityMeasure Phat]
    (hIP : ∀ φ : X × X → EReal, DiagDomFun φ → (∀ p, φ p ≠ ⊤) → ShortWDRODual.Legendre.IP Phat φ) :
    SelStar Phat := by sorry

end ShortWDRODual.IP
