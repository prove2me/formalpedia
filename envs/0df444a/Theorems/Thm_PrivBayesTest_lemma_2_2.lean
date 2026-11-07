-- Prove2me | Theorems.Thm_PrivBayesTest_lemma_2_2
-- name    : PrivBayesTest.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:24:51.153613+00:00
-- url     : https://prove2.me/theorems/91f4df91-c04c-4dcc-9617-2dd89300b521
-- title:
--   Lemma 2.2 (Lemma 2.1.1 of [JGB+26]): $\frac1n\mathrm{KL}(M(Q^n)\|M(P^n))\le\mathrm{KL}(Q'\|P)+\varepsilon\,\mathrm{TV}(Q',Q)$
-- statement:
--   Let $\varepsilon>0$, let $P,Q,Q'$ be probability measures on $\mathcal X$, let $n\ge1$, and let $M$ be an $\varepsilon$-DP mechanism from $\mathcal X^n$ to a measurable space $\mathcal Y$. Then
--
--   $$
--   \frac1n\,\mathrm{KL}\big(M(Q^n)\,\big\|\,M(P^n)\big) \;\le\; \mathrm{KL}(Q'\|P) + \varepsilon\,\mathrm{TV}(Q',Q).
--   $$
--
--   This is the KL bound for $\varepsilon$-DP mechanisms of Jacobsen et al. that the upper bound on the private Chernoff information (Lemma 2.1) rests on.
--
--   Differences from the source:
--   - encoding: (1/n) KL(M(Qⁿ) ∥ M(Pⁿ)) ≤ KL(Q′ ∥ P) + ε TV(Q′, Q) → KL(M(Qⁿ) ∥ M(Pⁿ)) ≤ n · (KL(Q′ ∥ P) + ε TV(Q′, Q)) in [0, ∞], with n ≥ 1; reason: equivalent for n ≥ 1
--   - encoding: ε-DP mechanism M (a randomized algorithm) → Markov kernel κ with PrivLearn.Generic.IsDP (replace-one neighbours); reason: a randomized algorithm is a Markov kernel; IsDP is Definition 1.1
-- source:
--   Jacobsen, Optimal Error Exponents for Private Bayesian Hypothesis Testing, STOC 2027 submission (manuscript sha256 abff2fdd66827f43…124ef), Lemma 2.2, p.9

import Mathlib
import Definitions.Def_PrivLearn_Generic_Privacy
import Definitions.Def_FoundationsRL_DECLower_tvDist
import Definitions.Def_PrivBayesTest_outLaw

open MeasureTheory ProbabilityTheory

namespace PrivBayesTest

/-- **Lemma 2.2** (Lemma 2.1.1 of [JGB+26]) of Jacobsen, *Optimal Error Exponents for Private Bayesian Hypothesis Testing*, STOC 2027 submission (manuscript sha256 abff2fdd…124ef), p.9. Let `P, Q, Q′` be distributions over `X` and
let `M : Xⁿ → Y` be an ε-DP mechanism. Then `(1/n) KL(M(Qⁿ) ∥ M(Pⁿ)) ≤ KL(Q′ ∥ P) + ε TV(Q′, Q)`.

**Formalization Note** The mechanism is a Markov kernel `κ : Xⁿ → Y` satisfying
`PrivLearn.Generic.IsDP`; `M(Pⁿ)` is `outLaw κ P`. The inequality is multiplied by `n ≥ 1` and
stated in `ENNReal`, which is equivalent. TV is `FoundationsRL.DECLower.tvDist`. -/
theorem lemma_2_2 {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (ε : ℝ) (hε : 0 < ε)
    (P Q Q' : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [IsProbabilityMeasure Q']
    (n : ℕ) (hn : 0 < n) (κ : Kernel (Fin n → X) Y) [IsMarkovKernel κ]
    (hκ : PrivLearn.Generic.IsDP (fun z => κ z) ε) :
    InformationTheory.klDiv (outLaw κ Q) (outLaw κ P) ≤
      (n : ENNReal) * (InformationTheory.klDiv Q' P
        + ENNReal.ofReal (ε * FoundationsRL.DECLower.tvDist Q' Q)) := by sorry

end PrivBayesTest
