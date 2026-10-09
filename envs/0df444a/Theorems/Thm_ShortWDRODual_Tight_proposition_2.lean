-- Prove2me | Theorems.Thm_ShortWDRODual_Tight_proposition_2
-- name    : ShortWDRODual.Tight.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:31:44.856244+00:00
-- url     : https://prove2.me/theorems/443c4120-aabf-4149-823e-ba2be4933e29
-- title:
--   Proposition 2, p. 7 — for tight ℙ̂ and ℙ̂-measurable f, φ(x̂, x) = f(x) − λd(x̂, x)^p is (ℱ ⊗ ℱ_ℙ̂)-measurable and satisfies (IP)
-- statement:
--   Let $(\mathcal X,d)$ be a metric space equipped with its Borel $\sigma$-algebra $\mathcal F$, let $\widehat{\mathbb P}$ be a tight probability measure on it (for every $\epsilon>0$ there is a compact $K$ with $\widehat{\mathbb P}(K^c)\le\epsilon$), and let $\mathcal F_{\widehat{\mathbb P}}$ be the completion of $\mathcal F$ under $\widehat{\mathbb P}$. Let $f:\mathcal X\to\mathbb R$ be $\widehat{\mathbb P}$-measurable with $\mathbb E_{\widehat{\mathbb P}}[f]>-\infty$, and let $p\in[1,\infty)$, $\lambda\ge0$. Put
--   $$\varphi(\widehat x,x)=f(x)-\lambda\,d(\widehat x,x)^p .$$
--   Then:
--
--   1. if $\mathcal X$ is separable, $\varphi$ is $(\mathcal F\otimes\mathcal F_{\widehat{\mathbb P}})$-measurable;
--   2. $\varphi$ satisfies the interchangeability principle: $\widehat x\mapsto\sup_x\varphi(\widehat x,x)$ is $\widehat{\mathbb P}$-measurable and
--   $$\mathbb E_{\widehat X\sim\widehat{\mathbb P}}\Big[\sup_{x\in\mathcal X}\varphi(\widehat X,x)\Big]=\sup_{\gamma\in\Gamma_{\widehat{\mathbb P}}}\mathbb E_{(\widehat X,X)\sim\gamma}[\varphi(\widehat X,X)],$$
--   where $\Gamma_{\widehat{\mathbb P}}$ is the set of probability measures on $\mathcal X\times\mathcal X$ with first marginal $\widehat{\mathbb P}$.
--
--   The result shows that the interchangeability principle, and with it the paper's strong duality for Wasserstein distributionally robust optimization, holds for the $p$-Wasserstein cost on any metric space under a tight nominal distribution, even when the loss $f$ is only measurable for the completed $\sigma$-algebra (as for value functions of Markov decision processes on Borel spaces).
--
--   **Formalization Note** Expectations are `extIntegral`: $\int\varphi^+-\int\varphi^-$ in the extended reals, with lower Lebesgue integrals and $\infty-\infty=-\infty$. Since $\varphi$ need not be $\mathcal F\otimes\mathcal F$-measurable, the page leaves $\mathbb E_\gamma[\varphi]$ undefined for general $\gamma\in\Gamma_{\widehat{\mathbb P}}$; the lower-integral reading is the one adopted, and $\Gamma_{\widehat{\mathbb P}}$ is kept on $\mathcal F\otimes\mathcal F$ as printed. "Tight measure" is Mathlib's `IsTightMeasureSet {Phat}`; $\widehat{\mathbb P}$ is a probability measure as in the paper's standing Assumption 1. $(\mathcal F\otimes\mathcal F_{\widehat{\mathbb P}})$-measurability is measurability on `X × NullMeasurableSpace X Phat`, whose second factor carries the completion. **Correction of the page:** clause 1 carries the hypothesis that $\mathcal X$ is separable. Without it the clause is false: on a discrete metric space of cardinality above the continuum, with $\widehat{\mathbb P}$ a Dirac mass, $f=0$ and $\lambda=p=1$, $\varphi=-\mathbf 1\{\widehat x\ne x\}$, and the diagonal is not in $2^{\mathcal X}\otimes2^{\mathcal X}$. Clause 2 is stated, as printed, for every metric space.
-- source:
--   Zhang, Yang & Gao, A Short and General Duality Proof for Wasserstein Distributionally Robust Optimization, arXiv:2205.00362v4, Proposition 2, p. 7 (PDF p. 7); (IP), p. 3 (PDF p. 3)

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_ShortWDRODual_Tight_Setting

namespace ShortWDRODual.Tight

open MeasureTheory ModelRiskOT.Duality

/-- Proposition 2, arXiv:2205.00362v4, p. 7. On a metric space with its Borel σ-algebra, for a
tight probability measure `ℙ̂`, a `ℙ̂`-measurable `f` with `𝔼_ℙ̂[f] > −∞`, `p ∈ [1, ∞)` and
`λ ≥ 0`, the function `φ(x̂, x) = f(x) − λ d(x̂, x)^p` is `(ℱ ⊗ ℱ_ℙ̂)`-measurable and
satisfies (IP).

Correction of the page: the `(ℱ ⊗ ℱ_ℙ̂)`-measurability clause is stated for separable `𝒳`.
Without separability it can fail (a discrete metric space of cardinality above the continuum,
`ℙ̂` a Dirac mass, `f = 0`, `λ = p = 1`: then `φ = −1_{x̂ ≠ x}` and the diagonal is not in
`ℱ ⊗ ℱ_ℙ̂ = 2^𝒳 ⊗ 2^𝒳`). The (IP) clause is stated for every metric space, as printed. -/
theorem proposition_2 {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (Phat : Measure X) [IsProbabilityMeasure Phat]
    (htight : IsTightMeasureSet ({Phat} : Set (Measure X)))
    (f : X → ℝ) (hf : NullMeasurable f Phat)
    (hfint : ⊥ < extIntegral Phat (fun x => (f x : EReal)))
    (p : ℝ) (hp : 1 ≤ p) (lam : ℝ) (hlam : 0 ≤ lam) :
    (TopologicalSpace.SeparableSpace X →
        @Measurable (X × NullMeasurableSpace X Phat) EReal _ _
          (fun q => pWassIntegrand f lam p (q.1, q.2))) ∧
      ShortWDRODual.Legendre.IPEq Phat (pWassIntegrand f lam p) := by sorry

end ShortWDRODual.Tight
