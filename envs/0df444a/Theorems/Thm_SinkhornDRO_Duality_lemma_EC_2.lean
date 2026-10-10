-- Prove2me | Theorems.Thm_SinkhornDRO_Duality_lemma_EC_2
-- name    : SinkhornDRO.Duality.lemma_EC_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:23:41.872484+00:00
-- url     : https://prove2.me/theorems/a781dc38-9285-4ea3-bdfe-2a5fca0c833c
-- title:
--   Lemma EC.2 — Gibbs variational principle: $v(\tau)=\tau\log\mathbb E_\nu[e^{f/\tau}]$
-- statement:
--   Let $\nu$ be a σ-finite measure on a measurable space $\mathcal Z$ such that some probability measure $\mathbb Q$ satisfies $\mathbb Q\ll\nu$, and let $f:\mathcal Z\to\mathbb R\cup\{\infty\}$ be measurable (with $f>-\infty$ $\nu$-almost everywhere). For $\tau\ge0$ let
--
--   $$
--   v(\tau)=\sup_{\mathbb P\ll\nu}\ \mathbb E_{z\sim\mathbb P}\Big[f(z)-\tau\log\frac{d\mathbb P(z)}{d\nu(z)}\Big].
--   $$
--
--   Then:
--   1. $v(0)=\operatorname{ess\,sup}_\nu f=\inf\{t:\nu\{f(z)>t\}=0\}$.
--   2. If $\tau>0$ and $\mathbb E_{z\sim\nu}[e^{f(z)/\tau}]<\infty$, then $v(\tau)=\tau\log\mathbb E_{z\sim\nu}[e^{f(z)/\tau}]$, and the supremum is attained at the Gibbs distribution $d\mathbb P(z)=\dfrac{e^{f(z)/\tau}}{\mathbb E_{u\sim\nu}[e^{f(u)/\tau}]}\,d\nu(z)$. Moreover, if $\mathbb E_{z\sim\nu}[e^{f(z)/\tau_0}]<\infty$ for some $\tau_0>0$, then $\lim_{\tau\downarrow0}v(\tau)=v(0)$.
--   3. If $\tau>0$ and $\mathbb E_{z\sim\nu}[e^{f(z)/\tau}]=\infty$, then $v(\tau)=\infty$.
--
--   The lemma evaluates the inner supremum of the Lagrangian relaxation of (Primal) in closed form; it is applied with $f-\lambda c(x,\cdot)$ in place of $f$ and $\tau=\lambda\epsilon$.
--
--   **Formalization Note** The limit "$\lim_{\tau\downarrow0}v(\tau)=v(0)$" is stated, as in the paper, under finiteness of $\mathbb E_\nu[e^{f/\tau_0}]$ at a single $\tau_0>0$ (the hypothesis of (II)); without any such $\tau_0$ it can fail (infinite $\nu$, bounded $f$: $v\equiv\infty$ on $\tau>0$). The limit is in the extended reals and includes the case $\operatorname{ess\,sup}_\nu f=\infty$. The hypothesis $f>-\infty$ is required only $\nu$-a.e., which is how the lemma is applied to $f-\lambda c(x,\cdot)$. σ-finiteness of $\nu$ is added: Radon–Nikodym derivatives need it.
-- source:
--   Wang, Gao, Xie, Sinkhorn Distributionally Robust Optimization, arXiv:2109.11926v5, p. ec13, Lemma EC.2 (citing [57, §2.1] / [100])

import Mathlib
import Definitions.Def_DupacovaWets_Consistency_expect
import Definitions.Def_SinkhornDRO_Duality_Gibbs

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open DupacovaWets.Consistency (expect)

namespace SinkhornDRO.Duality

/-- Lemma EC.2 (Gibbs variational principle), Wang, Gao, Xie, *Sinkhorn Distributionally Robust
Optimization*, arXiv:2109.11926v5, p. ec13. For a σ-finite reference measure `ν` that admits an
absolutely continuous probability measure, and a measurable `f : Z → ℝ ∪ {∞}` (`ν`-a.e.), the value
`v(τ) = sup_{P ≪ ν} E_P[f − τ log dP/dν]` satisfies
(I) `v(0) = ess sup_ν f`;
(II) for `τ > 0` with `E_ν[e^{f/τ}] < ∞`: `v(τ) = τ log E_ν[e^{f/τ}]`, attained at the Gibbs
measure `dP = e^{f/τ} / E_ν[e^{f/τ}] dν`; and `v(τ) → v(0)` as `τ ↓ 0` whenever
`E_ν[e^{f/τ₀}] < ∞` for some `τ₀ > 0`;
(III) for `τ > 0` with `E_ν[e^{f/τ}] = ∞`: `v(τ) = ∞`. -/
theorem lemma_EC_2 {Z : Type*} [MeasurableSpace Z] (ν : Measure Z) [SigmaFinite ν]
    (hQ : ∃ Q : Measure Z, IsProbabilityMeasure Q ∧ Q ≪ ν)
    (f : Z → EReal) (hf : Measurable f) (hf_bot : ∀ᵐ z ∂ν, f z ≠ ⊥) :
    -- (I)
    gibbsValue ν f 0 = essSup f ν ∧
    -- (II), value and optimal solution
    (∀ τ : ℝ, 0 < τ → ∫⁻ z, EReal.exp (((τ⁻¹ : ℝ) : EReal) * f z) ∂ν < ⊤ →
      gibbsValue ν f τ =
          (τ : EReal) * ENNReal.log (∫⁻ z, EReal.exp (((τ⁻¹ : ℝ) : EReal) * f z) ∂ν) ∧
        (let Pτ : Measure Z := (∫⁻ u, EReal.exp (((τ⁻¹ : ℝ) : EReal) * f u) ∂ν)⁻¹ •
            ν.withDensity (fun z => EReal.exp (((τ⁻¹ : ℝ) : EReal) * f z));
          IsProbabilityMeasure Pτ ∧ Pτ ≪ ν ∧
            expect Pτ (fun z => f z - (τ : EReal) * ENNReal.log (Pτ.rnDeriv ν z)) =
              gibbsValue ν f τ)) ∧
    -- (II), the limit τ ↓ 0
    (∀ τ₀ : ℝ, 0 < τ₀ → ∫⁻ z, EReal.exp (((τ₀⁻¹ : ℝ) : EReal) * f z) ∂ν < ⊤ →
      Filter.Tendsto (gibbsValue ν f) (nhdsWithin 0 (Set.Ioi 0)) (nhds (gibbsValue ν f 0))) ∧
    -- (III)
    (∀ τ : ℝ, 0 < τ → ∫⁻ z, EReal.exp (((τ⁻¹ : ℝ) : EReal) * f z) ∂ν = ⊤ →
      gibbsValue ν f τ = ⊤) := by sorry

end SinkhornDRO.Duality
