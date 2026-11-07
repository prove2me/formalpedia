-- Prove2me | Theorems.Thm_PrivBayesTest_lemma_B_1
-- name    : PrivBayesTest.lemma_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:24:05.960278+00:00
-- url     : https://prove2.me/theorems/075cf9c9-7a51-4ba0-89d7-634914bef332
-- title:
--   Lemma B.1 (group privacy): $\Pr[M(X)\in S]\le e^{k\varepsilon}\Pr[M(X')\in S]$ for inputs differing in at most $k$ entries
-- statement:
--   Let $\varepsilon>0$ and let $M$ be an $\varepsilon$-DP mechanism on $\mathcal D^n$ with output space $\mathcal O$: for all $x,x'$ differing in exactly one coordinate and every measurable $S$, $\Pr[M(x)\in S]\le e^\varepsilon\Pr[M(x')\in S]$. Let $x,x'\in\mathcal D^n$ differ in at most $k$ coordinates. Then
--
--   1. for every measurable $S\subseteq\mathcal O$,
--   $$
--   \Pr[M(x)\in S] \;\le\; e^{k\varepsilon}\,\Pr[M(x')\in S];
--   $$
--   2. the law of $M(x)$ is absolutely continuous with respect to that of $M(x')$, and its density satisfies $\log \frac{dM(x)}{dM(x')}\le k\varepsilon$ almost everywhere.
--
--   Group privacy is what lets the proof of Lemma 3.2 bound the likelihood ratio of a mechanism's output on two coupled datasets by $\varepsilon$ times the number of entries in which they differ.
--
--   Differences from the source:
--   - generalization: output laws of a randomized mechanism (probability measures) → any family of finite measures A(x) with the DP inequality; reason: the proof (a chain of k neighbour steps) uses only the DP inequality; probability measures are a special case
--   - encoding: inputs that differ in at most k entries → #{i | xᵢ ≠ x′ᵢ} ≤ k; reason: same condition
--   - encoding: log dM(X)/dM(X′) ≤ kε → M(X) ≪ M(X′) and dM(X)/dM(X′) ≤ e^{kε} M(X′)-almost everywhere; reason: the density exists only under absolute continuity, which the event bound gives; Radon–Nikodym derivatives are defined almost everywhere
-- source:
--   Jacobsen, Optimal Error Exponents for Private Bayesian Hypothesis Testing, STOC 2027 submission (manuscript sha256 abff2fdd66827f43…124ef), Lemma B.1, p.27

import Mathlib
import Definitions.Def_PrivLearn_Generic_Privacy

open MeasureTheory

namespace PrivBayesTest

/-- **Lemma B.1 (Group Privacy)** of Jacobsen, *Optimal Error Exponents for Private Bayesian Hypothesis Testing*, STOC 2027 submission (manuscript sha256 abff2fdd…124ef), p.27. Let `M` be ε-DP and let `X, X′` be inputs that
differ in at most `k` entries. Then `Pr[M(X) ∈ S] ≤ e^{kε} Pr[M(X′) ∈ S]` for every event `S`, and
the density satisfies `log(dM(X)/dM(X′)) ≤ kε`.

**Formalization Note** The output laws of the mechanism are given by `A : Xⁿ → Measure O`, required
to be finite measures (the paper's are probability measures). ε-DP is the published
`PrivLearn.Generic.IsDP` (replace-one neighbours, Definition 1.1, p.2). "Differ in at most `k`
entries" is `#{i | xᵢ ≠ x′ᵢ} ≤ k`. The density clause is stated as `M(X) ≪ M(X′)` together with
`dM(X)/dM(X′) ≤ e^{kε}` `M(X′)`-almost everywhere (hence also `M(X)`-almost everywhere). -/
theorem lemma_B_1 {D O : Type*} [MeasurableSpace O] {n : ℕ} (A : (Fin n → D) → Measure O)
    [∀ z, IsFiniteMeasure (A z)] (ε : ℝ) (hε : 0 < ε) (hA : PrivLearn.Generic.IsDP A ε) (k : ℕ)
    (z z' : Fin n → D) (hk : {i : Fin n | z i ≠ z' i}.ncard ≤ k) :
    (∀ S : Set O, MeasurableSet S → A z S ≤ ENNReal.ofReal (Real.exp (k * ε)) * A z' S) ∧
      A z ≪ A z' ∧
      ∀ᵐ y ∂(A z'), (A z).rnDeriv (A z') y ≤ ENNReal.ofReal (Real.exp (k * ε)) := by sorry

end PrivBayesTest
