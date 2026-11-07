-- Prove2me | Theorems.Thm_PrivBayesTest_lemma_B_3
-- name    : PrivBayesTest.lemma_B_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:24:38.6455+00:00
-- url     : https://prove2.me/theorems/856bbbd2-c9ef-494c-acca-7a90f8a4cac3
-- title:
--   Lemma B.3: variational representations of Rényi divergence, $-\log\int dP^\alpha dQ^{1-\alpha}$ as an infimum over $R$ and a supremum over $g$
-- statement:
--   Let $P,Q$ be probability measures on $\mathcal X$ and $\alpha\in(0,1)$. Then
--
--   1. (van Erven–Harremoës)
--   $$
--   -\log\int dP^\alpha dQ^{1-\alpha} \;=\; \inf_{R\in\Delta(\mathcal X)}\big\{\alpha\,\mathrm{KL}(R\|P)+(1-\alpha)\,\mathrm{KL}(R\|Q)\big\};
--   $$
--   2. (Birrell et al.)
--   $$
--   -\log\int dP^\alpha dQ^{1-\alpha} \;=\; \sup_{g}\Big\{-\alpha\log\int e^{(\alpha-1)g}\,dP-(1-\alpha)\log\int e^{\alpha g}\,dQ\Big\},
--   $$
--   the supremum over all measurable $g:\mathcal X\to\mathbb R$.
--
--   Both sides may equal $+\infty$ (when $P\perp Q$). Part 1 is used in the upper bound (Lemma 2.1); part 2, with $g(y)=\gamma y$, in the lower bound (Corollary 2.7).
--
--   Differences from the source:
--   - reading: sup_g with no class of g printed → supremum over all measurable g : X → ℝ; reason: Corollary 2.7 applies part 2 to the unbounded g(y) = γy, so the bounded-g reading would not support the paper's use
--   - encoding: real-valued exponents, divergences and suprema → extended reals (EReal/ENNReal) with −log 0 = +∞; reason: Lean convention; avoids junk values of real sup/inf; same instances
--   - encoding: ∫ dP^α dQ^{1−α} and ∫ e^{…} dP → lower integrals; the affinity uses densities with respect to P + Q; reason: same values; the affinity does not depend on the dominating measure
-- source:
--   Jacobsen, Optimal Error Exponents for Private Bayesian Hypothesis Testing, STOC 2027 submission (manuscript sha256 abff2fdd66827f43…124ef), Lemma B.3, p.27

import Mathlib
import Definitions.Def_PrivBayesTest_chernoff

open MeasureTheory

namespace PrivBayesTest

/-- **Lemma B.3 (Variational Representations of Rényi Divergence)** of Jacobsen, *Optimal Error Exponents for Private Bayesian Hypothesis Testing*, STOC 2027 submission (manuscript sha256 abff2fdd…124ef), p.27. For `α ∈ (0,1)` and
probability measures `P, Q` on `X`:
1. `−log ∫ dP^α dQ^{1−α} = inf_{R ∈ Δ(X)} {α KL(R ∥ P) + (1 − α) KL(R ∥ Q)}`;
2. `−log ∫ dP^α dQ^{1−α} = sup_g {−α log ∫ e^{(α−1)g} dP − (1 − α) log ∫ e^{αg} dQ}`.

**Formalization Note** All values are in `EReal`; both sides may be `+∞` (mutually singular
`P, Q`). The affinity is `PrivBayesTest.affinity` (densities with respect to `P + Q`). KL is
`InformationTheory.klDiv`. In part 2, `g` ranges over all measurable `g : X → ℝ` (the paper prints
"`sup_g`" without a class; Corollary 2.7 applies it to the unbounded `g(y) = γy`); the integrals are
lower integrals with values in `(0, ∞]`, so each term lies in `[−∞, ∞)`. -/
theorem lemma_B_3 {X : Type*} [MeasurableSpace X] (P Q : Measure X) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    -ENNReal.log (affinity α P Q) =
        ⨅ R : ProbabilityMeasure X, ((ENNReal.ofReal α * InformationTheory.klDiv (R : Measure X) P
          + ENNReal.ofReal (1 - α) * InformationTheory.klDiv (R : Measure X) Q : ENNReal) : EReal) ∧
      -ENNReal.log (affinity α P Q) =
        ⨆ (g : X → ℝ) (_ : Measurable g),
          (-((α : ℝ) : EReal) * ENNReal.log (∫⁻ x, ENNReal.ofReal (Real.exp ((α - 1) * g x)) ∂P)
            - ((1 - α : ℝ) : EReal) * ENNReal.log (∫⁻ x, ENNReal.ofReal (Real.exp (α * g x)) ∂Q)) := by sorry

end PrivBayesTest
