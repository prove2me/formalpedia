-- Prove2me | Theorems.Thm_ShortWDRODual_IP_proposition_1
-- name    : ShortWDRODual.IP.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:31:12.624008+00:00
-- url     : https://prove2.me/theorems/b951d987-87dc-4c2a-9f75-eac46140a266
-- title:
--   Proposition 1, p. 6 — (IP) holds for all diagonally dominant φ iff (Proj) and (Sel*) hold
-- statement:
--   Let $(\mathcal X,\mathcal F,\widehat{\mathbb P})$ be a probability space and $\mathcal F_{\widehat{\mathbb P}}$ the completion of $\mathcal F$ under $\widehat{\mathbb P}$. The following are equivalent:
--
--   1. every $(\mathcal F\otimes\mathcal F)$-measurable diagonally dominant function $\phi:\mathcal X\times\mathcal X\to\mathbb R\cup\{-\infty\}$ satisfies the interchangeability principle (IP): $\Phi(\widehat x)=\sup_x\phi(\widehat x,x)$ is $\widehat{\mathbb P}$-measurable and
--   $$\mathbb E_{\widehat X\sim\widehat{\mathbb P}}\Big[\sup_{x\in\mathcal X}\phi(\widehat X,x)\Big]=\sup_{\gamma\in\Gamma_{\widehat{\mathbb P}}}\mathbb E_{(\widehat X,X)\sim\gamma}\big[\phi(\widehat X,X)\big];$$
--   2. $(\mathcal X,\mathcal F,\widehat{\mathbb P})$ satisfies
--      - **(Proj)** for every diagonally dominant set $A\in\mathcal F\otimes\mathcal F$, $\mathrm{Proj}_{\widehat x}(A)=\{\widehat x:(\widehat x,x)\in A\text{ for some }x\}\in\mathcal F_{\widehat{\mathbb P}}$, and
--      - **(Sel\*)** for every diagonally dominant set-valued function $E:\mathcal X\to\mathcal F\setminus\{\emptyset\}$ with $\mathrm{Graph}(E)\in\mathcal F\otimes\mathcal F$ there is $\gamma\in\Gamma_{\widehat{\mathbb P}}$ with $\operatorname{supp}\gamma\subset\mathrm{Graph}(E)$.
--
--   Here $\Gamma_{\widehat{\mathbb P}}$ is the set of probability measures on $\mathcal X\times\mathcal X$ with first marginal $\widehat{\mathbb P}$. Together with Lemma 4 and Theorem 1 of the paper, this reduces strong duality for Wasserstein distributionally robust optimization to a measurable projection and a weak measurable selection property of the nominal probability space.
--
--   **Formalization Note** Expectations are `extIntegral` values in $[-\infty,\infty]$, with the undefined $\infty-\infty$ read as $-\infty$. $\widehat{\mathbb P}$-measurability is `NullMeasurable`/`NullMeasurableSet`. "$\operatorname{supp}\gamma\subset\mathrm{Graph}(E)$" is read as $\gamma(\mathrm{Graph}(E)^c)=0$, since $\mathcal X$ carries no topology.
-- source:
--   Zhang, Yang & Gao, A Short and General Duality Proof for Wasserstein Distributionally Robust Optimization, arXiv:2205.00362v4, Proposition 1, p. 6 (PDF p. 6); proof in Appendix EC.2, pp. ec2–ec4 (PDF pp. 16–18)

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_ShortWDRODual_IP_Setting

namespace ShortWDRODual.IP

open MeasureTheory ModelRiskOT.Duality
open scoped ENNReal

theorem proposition_1 {X : Type*} [MeasurableSpace X] (Phat : Measure X)
    [IsProbabilityMeasure Phat] :
    (∀ φ : X × X → EReal, DiagDomFun φ → (∀ p, φ p ≠ ⊤) → ShortWDRODual.Legendre.IP Phat φ) ↔
      (Proj Phat ∧ SelStar Phat) := by sorry

end ShortWDRODual.IP
