-- Prove2me | Theorems.Thm_PrivBayesTest_corollary_2_7
-- name    : PrivBayesTest.corollary_2_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:25:19.340224+00:00
-- url     : https://prove2.me/theorems/0a2a1875-154a-4d37-af3c-82c9ba42a0cd
-- title:
--   Corollary 2.7: $C(M_{\mathrm{Lap}}(P^n);M_{\mathrm{Lap}}(Q^n))\ge(n-1)V-\log n$
-- statement:
--   In the setting of Lemma 2.6 ($\alpha\in(0,1)$, $\bar\ell$ bounded and measurable with $\int e^{(\alpha-1)\bar\ell}dP=\int e^{\alpha\bar\ell}dQ$, $V=-\log\mathbb E_Q[e^{\alpha\bar\ell}]$ and $M_{\mathrm{Lap}}=\sum_i\bar\ell(X_i)+\mathrm{Lap}(1/(1-\tilde\alpha))$), for every $n\ge1$,
--
--   $$
--   C\big(M_{\mathrm{Lap}}(P^n);\,M_{\mathrm{Lap}}(Q^n)\big)\;\ge\;(n-1)V-\log n ,
--   $$
--
--   where $C$ is the Chernoff information. With the optimal $\alpha$ and $\bar\ell$, this is the lower bound on the private Chernoff information that closes the strong duality of Theorem 1.3.
--
--   Differences from the source:
--   - generalization: ℓ̄ the clipped log-likelihood ratio of the dual optimizer at α → any bounded measurable ℓ̄ : X → ℝ with ∫ e^{(α−1)ℓ̄} dP = ∫ e^{αℓ̄} dQ; reason: the proof uses only the balancing condition and the Laplace scale; the paper's ℓ̄ is bounded (clipped) and balanced by Proposition 2.5 item 4
--   - encoding: M_Lap(Pⁿ), M_Lap(Qⁿ) → lapLaw ℓ̄ (1/(1 − α̃)) n P (resp. Q), the image of Pⁿ ⊗ Lap(1/(1 − α̃)) under (x, z) ↦ Σᵢ ℓ̄(xᵢ) + z; reason: the output law of M_Lap(X) = σ(X) + Z with Z independent of X
--   - encoding: real-valued exponents, divergences and suprema → extended reals (EReal/ENNReal) with −log 0 = +∞; reason: Lean convention; avoids junk values of real sup/inf; same instances
-- source:
--   Jacobsen, Optimal Error Exponents for Private Bayesian Hypothesis Testing, STOC 2027 submission (manuscript sha256 abff2fdd66827f43…124ef), Corollary 2.7, p.13

import Mathlib
import Definitions.Def_PrivBayesTest_chernoff
import Definitions.Def_PrivBayesTest_klTvValue
import Definitions.Def_PrivBayesTest_lapLaw

open MeasureTheory

namespace PrivBayesTest

/-- **Corollary 2.7** of Jacobsen, *Optimal Error Exponents for Private Bayesian Hypothesis Testing*, STOC 2027 submission (manuscript sha256 abff2fdd…124ef), p.13. Let `V = −log E_Q[e^{αℓ̄}] = −log E_P[e^{(α−1)ℓ̄}]`. For every `n ≥ 1`,
`C(M_Lap(Pⁿ); M_Lap(Qⁿ)) ≥ (n − 1)V − log n`.

**Formalization Note** Same setting as Lemma 2.6: any bounded measurable `ℓ̄` with the balancing
condition, `M_Lap = Σᵢ ℓ̄(Xᵢ) + Lap(1/(1 − α̃))` with output laws `lapLaw`. `C` is the Chernoff
information `PrivBayesTest.chernoff` (in `EReal`). -/
theorem corollary_2_7 {X : Type*} [MeasurableSpace X] (P Q : Measure X) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1) (ℓbar : X → ℝ)
    (hℓm : Measurable ℓbar) (hℓb : ∃ C : ℝ, ∀ x, |ℓbar x| ≤ C)
    (hbal : ∫ x, Real.exp ((α - 1) * ℓbar x) ∂P = ∫ x, Real.exp (α * ℓbar x) ∂Q)
    (n : ℕ) (hn : 1 ≤ n) :
    ((((n : ℝ) - 1) * -Real.log (∫ x, Real.exp (α * ℓbar x) ∂Q) - Real.log n : ℝ) : EReal) ≤
      chernoff (lapLaw ℓbar (1 / (1 - alphaTilde α)) n P)
        (lapLaw ℓbar (1 / (1 - alphaTilde α)) n Q) := by sorry

end PrivBayesTest
