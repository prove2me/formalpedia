-- Prove2me | Theorems.Thm_PrivBayesTest_lemma_2_6
-- name    : PrivBayesTest.lemma_2_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:25:24.462075+00:00
-- url     : https://prove2.me/theorems/7db90031-0047-431d-bc18-b5b9af30ef1e
-- title:
--   Lemma 2.6: $\mathbb E_Q[e^{\gamma\alpha M_{\mathrm{Lap}}(X)}]\le e^{-\gamma nV}/(1-\gamma^2)$ and the same bound under $P$
-- statement:
--   Let $P,Q$ be probability measures on $\mathcal X$, $\alpha\in(0,1)$, $\tilde\alpha=\min(\alpha,1-\alpha)$, and let $\bar\ell:\mathcal X\to\mathbb R$ be bounded and measurable with
--   $\int e^{(\alpha-1)\bar\ell}dP=\int e^{\alpha\bar\ell}dQ$. Let $V=-\log\mathbb E_Q[e^{\alpha\bar\ell}]=-\log\mathbb E_P[e^{(\alpha-1)\bar\ell}]$ and $M_{\mathrm{Lap}}(X)=\sum_{i=1}^n\bar\ell(X_i)+Z$ with $Z\sim\mathrm{Lap}(1/(1-\tilde\alpha))$ independent of $X$. For every $n\ge1$ and $\gamma\in(0,1)$,
--
--   $$
--   \mathbb E_{X\sim Q^n}\big[e^{\gamma\alpha M_{\mathrm{Lap}}(X)}\big]\le\frac{e^{-\gamma nV}}{1-\gamma^2},\qquad
--   \mathbb E_{X\sim P^n}\big[e^{-\gamma(1-\alpha)M_{\mathrm{Lap}}(X)}\big]\le\frac{e^{-\gamma nV}}{1-\gamma^2}.
--   $$
--
--   These moment bounds control both error probabilities of the Laplace test and its Chernoff information (Corollary 2.7, Lemma 3.3).
--
--   Differences from the source:
--   - generalization: ℓ̄ the clipped log-likelihood ratio of the dual optimizer at α → any bounded measurable ℓ̄ : X → ℝ with ∫ e^{(α−1)ℓ̄} dP = ∫ e^{αℓ̄} dQ; reason: the proof uses only the balancing condition and the Laplace scale; the paper's ℓ̄ is bounded (clipped) and balanced by Proposition 2.5 item 4
--   - encoding: E_Q[e^{γαM_Lap(X)}] → lower integral of e^{γαy} against the law lapLaw ℓ̄ (1/(1 − α̃)) n Q of M_Lap(X); reason: same expectation of a nonnegative variable
-- source:
--   Jacobsen, Optimal Error Exponents for Private Bayesian Hypothesis Testing, STOC 2027 submission (manuscript sha256 abff2fdd66827f43…124ef), Lemma 2.6, p.12

import Mathlib
import Definitions.Def_PrivBayesTest_klTvValue
import Definitions.Def_PrivBayesTest_lapLaw

open MeasureTheory

namespace PrivBayesTest

/-- **Lemma 2.6** of Jacobsen, *Optimal Error Exponents for Private Bayesian Hypothesis Testing*, STOC 2027 submission (manuscript sha256 abff2fdd…124ef), p.12. Let `V = −log E_Q[e^{αℓ̄}] = −log E_P[e^{(α−1)ℓ̄}]`. For every `n ≥ 1` and
every `γ ∈ (0,1)`,
`E_Q[e^{γα M_Lap(X)}] ≤ e^{−γnV}/(1 − γ²)` and `E_P[e^{−γ(1−α) M_Lap(X)}] ≤ e^{−γnV}/(1 − γ²)`,
where `M_Lap(X) = Σᵢ ℓ̄(Xᵢ) + Z`, `Z ∼ Lap(1/(1 − α̃))`.

**Formalization Note** Stated for every bounded measurable `ℓ̄ : X → ℝ` satisfying the balancing
condition `∫ e^{(α−1)ℓ̄} dP = ∫ e^{αℓ̄} dQ` (this contains the paper's clipped log-likelihood ratio,
Proposition 2.5). The integrands of the balancing condition and of `V` are bounded and measurable, so
the Bochner integrals are the true expectations. The law of `M_Lap(X)` under `X ∼ Qⁿ` is
`lapLaw ℓ̄ (1/(1 − α̃)) n Q`; the left-hand expectations are lower integrals in `ENNReal`. -/
theorem lemma_2_6 {X : Type*} [MeasurableSpace X] (P Q : Measure X) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1) (ℓbar : X → ℝ)
    (hℓm : Measurable ℓbar) (hℓb : ∃ C : ℝ, ∀ x, |ℓbar x| ≤ C)
    (hbal : ∫ x, Real.exp ((α - 1) * ℓbar x) ∂P = ∫ x, Real.exp (α * ℓbar x) ∂Q)
    (n : ℕ) (hn : 1 ≤ n) (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    ∫⁻ y, ENNReal.ofReal (Real.exp (γ * α * y)) ∂(lapLaw ℓbar (1 / (1 - alphaTilde α)) n Q) ≤
        ENNReal.ofReal (Real.exp (-γ * n * -Real.log (∫ x, Real.exp (α * ℓbar x) ∂Q)) / (1 - γ ^ 2)) ∧
      ∫⁻ y, ENNReal.ofReal (Real.exp (-γ * (1 - α) * y)) ∂(lapLaw ℓbar (1 / (1 - alphaTilde α)) n P) ≤
        ENNReal.ofReal (Real.exp (-γ * n * -Real.log (∫ x, Real.exp (α * ℓbar x) ∂Q)) / (1 - γ ^ 2)) := by sorry

end PrivBayesTest
