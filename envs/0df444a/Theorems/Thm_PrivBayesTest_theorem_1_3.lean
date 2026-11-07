-- Prove2me | Theorems.Thm_PrivBayesTest_theorem_1_3
-- name    : PrivBayesTest.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:26:06.158977+00:00
-- url     : https://prove2.me/theorems/15e5923a-2ab7-4888-b971-29b917d36ffa
-- title:
--   Theorem 1.3: $C_\varepsilon(P;Q)=\sup_{\alpha\in(0,1)}\inf_{R,S}\{\alpha\mathrm{KL}(R\|P)+(1-\alpha)\mathrm{KL}(S\|Q)+\tilde\alpha\varepsilon\mathrm{TV}(R,S)\}$
-- statement:
--   Let $\varepsilon>0$, $\tilde\alpha=\min(\alpha,1-\alpha)$, and let $P,Q$ be probability measures on $\mathcal X$. Then the sequence $c_n=\sup_{M\ \varepsilon\text{-DP}}\frac1nC(M(P^n);M(Q^n))$ of Definition 1.2 converges, and its limit, the private Chernoff information, is
--
--   $$
--   C_\varepsilon(P;Q)\;=\;\sup_{\alpha\in(0,1)}\ \inf_{R,S\in\Delta(\mathcal X)^2}\Big\{\alpha\mathrm{KL}(R\|P)+(1-\alpha)\mathrm{KL}(S\|Q)+\tilde\alpha\varepsilon\mathrm{TV}(R,S)\Big\}.
--   $$
--
--   This strong duality turns the supremum over all private mechanisms into a convex optimization over pairs of distributions, and drives both halves of Theorem 3.1.
--
--   Differences from the source:
--   - generalization: C_ε(P; Q) = sup_α inf_{R,S} {…} → additionally: the Definition 1.2 sequence converges to sup_α inf_{R,S} {…}; reason: makes explicit the limit that Definition 1.2 presupposes; §2.4 proves it
--   - encoding: sup over ε-DP mechanisms M → sup over output spaces Y : Type with any σ-algebra and ε-DP Markov kernels to Y; reason: contains every output space the paper uses (ℝ for the Laplace mechanism)
--   - encoding: real-valued exponents, divergences and suprema → extended reals (EReal/ENNReal) with −log 0 = +∞; reason: Lean convention; avoids junk values of real sup/inf; same instances
-- source:
--   Jacobsen, Optimal Error Exponents for Private Bayesian Hypothesis Testing, STOC 2027 submission (manuscript sha256 abff2fdd66827f43…124ef), Theorem 1.3, p.5 (proof §2.4, p.13)

import Mathlib
import Definitions.Def_PrivBayesTest_privChernoff
import Definitions.Def_PrivBayesTest_klTvValue

open MeasureTheory Filter Topology

namespace PrivBayesTest

/-- **Theorem 1.3** of Jacobsen, *Optimal Error Exponents for Private Bayesian Hypothesis Testing*, STOC 2027 submission (manuscript sha256 abff2fdd…124ef), p.5 (proved in §2.4, p.13). Let `ε > 0` and `α̃ = min(α, 1 − α)`. For any
probability measures `P, Q` on `X`,
`C_ε(P; Q) = sup_{α∈(0,1)} inf_{R,S∈Δ(X)²} {α KL(R ∥ P) + (1 − α) KL(S ∥ Q) + α̃ ε TV(R, S)}`.

**Formalization Note** `C_ε = privChernoff` is the `limUnder` of the sequence of Definition 1.2; the
second conjunct states that this sequence converges, to the same value (the printed definition
presupposes the limit; §2.4 proves it). Values in `EReal`. -/
theorem theorem_1_3 {X : Type*} [MeasurableSpace X] (ε : ℝ) (hε : 0 < ε) (P Q : Measure X)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    privChernoff ε P Q = klTvValue ε P Q ∧
      Tendsto (chernoffSeq ε P Q) atTop (𝓝 (klTvValue ε P Q)) := by sorry

end PrivBayesTest
