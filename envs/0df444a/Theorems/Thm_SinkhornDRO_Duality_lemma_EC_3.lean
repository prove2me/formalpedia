-- Prove2me | Theorems.Thm_SinkhornDRO_Duality_lemma_EC_3
-- name    : SinkhornDRO.Duality.lemma_EC_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:23:43.406224+00:00
-- url     : https://prove2.me/theorems/5b69784a-d1d5-49ac-9a3c-caaeaadb4a57
-- title:
--   Lemma EC.3 — measurability of $x\mapsto v_x(\lambda)$
-- statement:
--   Let $\widehat{\mathbb P}$ be a probability measure and $\nu$ a σ-finite measure on a measurable space $\mathcal Z$, let $\epsilon>0$, and assume Assumptions 1(I)–(III): the cost $c:\mathcal Z\times\mathcal Z\to[0,\infty]$ is measurable and finite $\nu$-a.e. in $z$ for $\widehat{\mathbb P}$-a.e. $x$; $\mathbb E_{z\sim\nu}[e^{-c(x,z)/\epsilon}]<\infty$ for $\widehat{\mathbb P}$-a.e. $x$; and $f:\mathcal Z\to\mathbb R\cup\{\infty\}$ is measurable. For $\lambda\ge0$ let
--
--   $$
--   v_x(\lambda)=\sup_{\gamma_x\in\mathcal P(\mathcal Z)}\ \mathbb E_{z\sim\gamma_x}\Big[f(z)-\lambda c(x,z)-\lambda\epsilon\log\frac{d\gamma_x(z)}{d\nu(z)}\Big].
--   $$
--
--   Then, for every fixed $\lambda\ge0$, the function $x\mapsto v_x(\lambda)$ is measurable with respect to $x\sim\widehat{\mathbb P}$.
--
--   The lemma makes the expectation $\mathbb E_{x\sim\widehat{\mathbb P}}[v_x(\lambda)]$ in the weak-duality bound meaningful.
--
--   **Formalization Note** The paper defines $v_x(\lambda)$ on $\operatorname{supp}\widehat{\mathbb P}$; here it is defined for every $x$ and the conclusion is $\widehat{\mathbb P}$-almost-everywhere measurability (`AEMeasurable`), which is what "measurable with respect to $x\sim\widehat{\mathbb P}$" requires. The supremum ranges over $\gamma_x\ll\nu$.
-- source:
--   Wang, Gao, Xie, Sinkhorn Distributionally Robust Optimization, arXiv:2109.11926v5, p. ec13, Lemma EC.3

import Mathlib
import Definitions.Def_DupacovaWets_Consistency_expect
import Definitions.Def_SinkhornDRO_Duality_Dual
import Definitions.Def_SinkhornDRO_Duality_Gibbs

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open DupacovaWets.Consistency (expect)

namespace SinkhornDRO.Duality

/-- Lemma EC.3 (measurability of `v_x(λ)`), Wang, Gao, Xie, *Sinkhorn Distributionally Robust
Optimization*, arXiv:2109.11926v5, p. ec13. Under Assumptions 1(I), 1(II), 1(III), for every fixed
`λ ≥ 0` the function `x ↦ v_x(λ) = sup_{γ_x} E_{γ_x}[f − λc(x,·) − λε log dγ_x/dν]` is measurable
with respect to `x ∼ P̂` (here: `P̂`-almost-everywhere measurable, as a function on all of `Z`). -/
theorem lemma_EC_3 {Z : Type*} [MeasurableSpace Z]
    (Phat ν : Measure Z) [IsProbabilityMeasure Phat] [SigmaFinite ν]
    (c : Z → Z → ℝ≥0∞) (ε : ℝ) (hε : 0 < ε) (f : Z → EReal)
    (hc_meas : Measurable (Function.uncurry c))
    (hc_fin : ∀ᵐ x ∂Phat, ∀ᵐ z ∂ν, c x z ≠ ⊤)
    (hZ_fin : ∀ᵐ x ∂Phat, normalizer ν c ε x < ⊤)
    (hf_meas : Measurable f) (hf_bot : ∀ z, f z ≠ ⊥) :
    ∀ lam : ℝ, 0 ≤ lam → AEMeasurable (fun x => vx ν c ε f lam x) Phat := by sorry

end SinkhornDRO.Duality
