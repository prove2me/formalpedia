-- Prove2me | Theorems.Thm_SinkhornDRO_Duality_lemma_2
-- name    : SinkhornDRO.Duality.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:23:26.719408+00:00
-- url     : https://prove2.me/theorems/14efde3e-4516-41a8-8225-509238f5130d
-- title:
--   Lemma 2 — (Primal) as a KL-constrained problem over conditional distributions
-- statement:
--   Under the standing assumptions ($\widehat{\mathbb P}$ a probability measure, $\nu\ne0$ σ-finite, $\epsilon>0$, $\bar\rho$ finite) and Assumption 1, the primal value of Sinkhorn DRO equals
--
--   $$
--   V=\sup_{\{\gamma_x\}}\Big\{\mathbb E_{x\sim\widehat{\mathbb P}}\mathbb E_{z\sim\gamma_x}[f(z)]\ :\ \epsilon\,\mathbb E_{x\sim\widehat{\mathbb P}}\mathbb E_{z\sim\gamma_x}\Big[\log\frac{d\gamma_x(z)}{d\mathbb Q_{x,\epsilon}(z)}\Big]\le\bar\rho\Big\},
--   $$
--
--   the supremum ranging over families $\{\gamma_x\}$ of probability distributions on $\mathcal Z$ indexed by $x$ (Markov kernels). The constraint says that the $\widehat{\mathbb P}$-average Kullback–Leibler divergence $D_{\mathrm{KL}}(\gamma_x\,\|\,\mathbb Q_{x,\epsilon})$ is at most $\bar\rho/\epsilon$.
--
--   Since the divergence is nonnegative and vanishes at $\gamma_x=\mathbb Q_{x,\epsilon}$, this reformulation yields the feasibility criterion $\bar\rho\ge0$ of Theorem 1(I).
--
--   **Formalization Note** The family $\{\gamma_x\}_{x\in\operatorname{supp}\widehat{\mathbb P}}$ is a Markov kernel $\kappa$ on all of $\mathcal Z$. The inner term $\mathbb E_{\gamma_x}[\log d\gamma_x/d\mathbb Q_{x,\epsilon}]$ is Mathlib's `klDiv` (equal to $+\infty$ when $\gamma_x\not\ll\mathbb Q_{x,\epsilon}$), averaged by a lower Lebesgue integral; the constraint is compared in the extended reals, so a negative $\bar\rho$ makes it infeasible. The objective $\mathbb E_{x\sim\widehat{\mathbb P}}\mathbb E_{z\sim\gamma_x}[f]$ is the expectation of $f$ under the mixture $\mathbb P=\int\gamma_x\,d\widehat{\mathbb P}(x)$, i.e. the primal objective of the distribution the kernel induces.
-- source:
--   Wang, Gao, Xie, Sinkhorn Distributionally Robust Optimization, arXiv:2109.11926v5, p. 12, Lemma 2 (proof p. ec14)

import Mathlib
import Definitions.Def_DupacovaWets_Consistency_expect
import Definitions.Def_SinkhornDRO_Duality_SinkhornDistance
import Definitions.Def_SinkhornDRO_Duality_Dual

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open DupacovaWets.Consistency (expect)

namespace SinkhornDRO.Duality

/-- Lemma 2 (reformulation of (Primal)), Wang, Gao, Xie, *Sinkhorn Distributionally Robust
Optimization*, arXiv:2109.11926v5, p. 12. Under Assumption 1,
`V = sup_{γ_x} { E_{x∼P̂} E_{z∼γ_x}[f(z)] : ε E_{x∼P̂} E_{z∼γ_x}[log dγ_x/dQ_{x,ε}] ≤ ρ̄ }`.
The family `{γ_x}` is a Markov kernel `κ`, the constraint is
`ε · E_{x∼P̂}[KL(κ x ‖ Q_{x,ε})] ≤ ρ̄`, and the objective is `E_{z∼P}[f(z)]` for the mixture
`P = ∫ κ x dP̂(x)` (the second marginal of `P̂ ⊗ κ`). -/
theorem lemma_2 {Z : Type*} [MeasurableSpace Z]
    (Phat ν : Measure Z) [IsProbabilityMeasure Phat] [SigmaFinite ν] (hν : ν ≠ 0)
    (c : Z → Z → ℝ≥0∞) (ε ρ : ℝ) (hε : 0 < ε) (f : Z → EReal)
    (hA : Assumption1 Phat ν c ε f)
    (hlog : Integrable (fun x => Real.log (normalizer ν c ε x).toReal) Phat) :
    primalValue Phat ν c ε ρ f =
      ⨆ κ ∈ {κ : Kernel Z Z | IsMarkovKernel κ ∧
          (ε : EReal) * ((∫⁻ x, InformationTheory.klDiv (κ x) (Qker ν c ε x) ∂Phat : ℝ≥0∞) : EReal)
            ≤ (rhoBar Phat ν c ε ρ : EReal)},
        expect (κ ∘ₘ Phat) f := by sorry

end SinkhornDRO.Duality
