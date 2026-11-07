-- Prove2me | Theorems.Thm_PrivBayesTest_lemma_2_1
-- name    : PrivBayesTest.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:26:14.134024+00:00
-- url     : https://prove2.me/theorems/f3bcb002-0f0a-43e0-873d-5d3aba70423b
-- title:
--   Lemma 2.1: $C_\varepsilon(P;Q)\le\sup_\alpha\inf_{R,S}F_\alpha(R,S)$, and the same bound for each $n$ and each mechanism
-- statement:
--   Let $\varepsilon>0$ and let $P,Q$ be probability measures on $\mathcal X$. Write $F_\alpha(R,S)=\alpha\mathrm{KL}(R\|P)+(1-\alpha)\mathrm{KL}(S\|Q)+\tilde\alpha\varepsilon\mathrm{TV}(R,S)$ with $\tilde\alpha=\min(\alpha,1-\alpha)$. Then:
--
--   1. for every $n\ge1$, every measurable output space $\mathcal Y$ and every $\varepsilon$-DP mechanism $M$ from $\mathcal X^n$ to $\mathcal Y$,
--   $$
--   \frac1n\,C\big(M(P^n);M(Q^n)\big) \;\le\; \sup_{\alpha\in(0,1)}\ \inf_{R,S\in\Delta(\mathcal X)^2} F_\alpha(R,S);
--   $$
--   2. consequently
--   $$
--   C_\varepsilon(P;Q) \;\le\; \sup_{\alpha\in(0,1)}\ \inf_{R,S\in\Delta(\mathcal X)^2} F_\alpha(R,S).
--   $$
--
--   This is the upper half of the strong duality of Theorem 1.3.
--
--   Differences from the source:
--   - generalization: C_ε(P; Q) ≤ sup_α inf_{R,S} F_α(R, S) → additionally the bound (1/n) C(M(Pⁿ); M(Qⁿ)) ≤ sup_α inf_{R,S} F_α for every n ≥ 1, every output space and every ε-DP mechanism; reason: this is what the proof establishes (display (4) and its supremum over α); the printed statement is the second conjunct
--   - encoding: C_ε(P; Q) := lim → privChernoff, the limUnder of the Definition 1.2 sequence; reason: the limit exists (Theorem 1.3); the per-n conjunct does not depend on it
--   - encoding: ε-DP mechanism M (a randomized algorithm) → Markov kernel κ with PrivLearn.Generic.IsDP (replace-one neighbours); reason: a randomized algorithm is a Markov kernel; IsDP is Definition 1.1
--   - encoding: real-valued exponents, divergences and suprema → extended reals (EReal/ENNReal) with −log 0 = +∞; reason: Lean convention; avoids junk values of real sup/inf; same instances
-- source:
--   Jacobsen, Optimal Error Exponents for Private Bayesian Hypothesis Testing, STOC 2027 submission (manuscript sha256 abff2fdd66827f43…124ef), Lemma 2.1, p.9

import Mathlib
import Definitions.Def_PrivLearn_Generic_Privacy
import Definitions.Def_PrivBayesTest_privChernoff
import Definitions.Def_PrivBayesTest_klTvValue

open MeasureTheory ProbabilityTheory

namespace PrivBayesTest

/-- **Lemma 2.1** of Jacobsen, *Optimal Error Exponents for Private Bayesian Hypothesis Testing*, STOC 2027 submission (manuscript sha256 abff2fdd…124ef), p.9. For any `ε > 0` and probability measures `P, Q`,
`C_ε(P; Q) ≤ sup_{α∈(0,1)} inf_{R,S∈Δ(X)²} α KL(R ∥ P) + (1 − α) KL(S ∥ Q) + α̃ ε TV(R, S)`.

The first conjunct is the bound the proof establishes for each sample size: for every `n ≥ 1`,
every output space `Y` and every ε-DP mechanism `κ`, `(1/n) C(M(Pⁿ); M(Qⁿ))` is at most the
right-hand side. The second conjunct is the printed statement about `C_ε = privChernoff`.

**Formalization Note** Values in `EReal`. Mechanisms are ε-DP Markov kernels (`PrivLearn.Generic.IsDP`);
in the first conjunct `Y` ranges over all types with a σ-algebra. `privChernoff` is the `limUnder` of
Definition 1.2; the convergence of that sequence is part of Theorem 1.3 and Theorem 3.1. -/
theorem lemma_2_1 {X : Type*} [MeasurableSpace X] (ε : ℝ) (hε : 0 < ε) (P Q : Measure X)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    (∀ (Y : Type*) [MeasurableSpace Y] (n : ℕ), 0 < n → ∀ (κ : Kernel (Fin n → X) Y),
        IsMarkovKernel κ → PrivLearn.Generic.IsDP (fun z => κ z) ε →
          (((n : ℝ)⁻¹ : ℝ) : EReal) * chernoff (outLaw κ P) (outLaw κ Q) ≤ klTvValue ε P Q) ∧
      privChernoff ε P Q ≤ klTvValue ε P Q := by sorry

end PrivBayesTest
