-- Prove2me | Theorems.Thm_ShortWDRODual_IP_lemma_4
-- name    : ShortWDRODual.IP.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:31:25.741851+00:00
-- url     : https://prove2.me/theorems/0ac62291-658e-46ac-9b42-7a47099e5bdb
-- title:
--   Lemma 4, p. 13 — φ is diagonally dominant iff φ(x̂, x) = f(x) − λc(x̂, x) with c ≥ 0 vanishing on the diagonal
-- statement:
--   Let $(\mathcal X,\mathcal F)$ be a measurable space and $\phi:\mathcal X\times\mathcal X\to\mathbb R\cup\{-\infty\}$. Then $\phi$ is diagonally dominant (in particular $(\mathcal F\otimes\mathcal F)$-measurable) if and only if there exist a measurable function $f:\mathcal X\to\mathbb R\cup\{-\infty\}$, a constant $\lambda\ge0$, and a measurable function $c:\mathcal X\times\mathcal X\to[0,\infty]$ with $c(x,x)=0$ for all $x$, such that
--
--   $$\phi(\widehat x,x)=f(x)-\lambda c(\widehat x,x)\qquad\text{for all }\widehat x,x\in\mathcal X.$$
--
--   The products follow the convention $0\cdot\infty=\infty$. The lemma identifies the diagonally dominant functions with the family $f-\lambda c$ appearing in the dual problem (D) of Theorem 1, which is how Proposition 1 applies to Wasserstein DRO.
--
--   **Formalization Note** The lemma's $f$ is named $g$ in Lean. $\lambda c$ is `lamMul λ (c x̂ x)`, which is $+\infty$ when $c=\infty$ (also for $\lambda=0$). $c$ is curried, $c\,\widehat x\,x=c(\widehat x,x)$, and its measurability is that of the uncurried map on $\mathcal X\times\mathcal X$. The subtraction is `EReal` subtraction, so $-\infty-\infty=-\infty$.
-- source:
--   Zhang, Yang & Gao, A Short and General Duality Proof for Wasserstein Distributionally Robust Optimization, arXiv:2205.00362v4, Lemma 4, p. 13 (PDF p. 13); proof p. ec2 (PDF p. 16)

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_ShortWDRODual_IP_Setting

namespace ShortWDRODual.IP

open MeasureTheory ModelRiskOT.Duality
open scoped ENNReal

theorem lemma_4 {X : Type*} [MeasurableSpace X] (φ : X × X → EReal)
    (hφtop : ∀ p, φ p ≠ ⊤) :
    DiagDomFun φ ↔
      ∃ (g : X → EReal) (lam : ℝ) (c : X → X → ℝ≥0∞),
        Measurable g ∧ (∀ x, g x ≠ ⊤) ∧ 0 ≤ lam ∧
          Measurable (fun p : X × X => c p.1 p.2) ∧ (∀ x, c x x = 0) ∧
            ∀ xh x, φ (xh, x) = g x - ShortWDRODual.Legendre.lamMul lam (c xh x) := by sorry

end ShortWDRODual.IP
