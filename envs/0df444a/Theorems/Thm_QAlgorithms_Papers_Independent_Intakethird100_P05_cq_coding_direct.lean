-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P05_cq_coding_direct
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P05.cq_coding_direct
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T03:56:40.613982+00:00
-- url     : https://prove2.me/theorems/8daef948-e9f3-419e-969f-2d5af66ce1ad
-- title:
--   Direct stationary memoryless cq channel coding
-- statement:
--   Let $\mathcal X$ be a finite alphabet, let $\rho_x$ be density operators on a finite-dimensional complex Hilbert space $\mathcal H$, and let $p$ be a probability law on $\mathcal X$. Put $\sigma=\sum_xp(x)\rho_x$ and $I(p)=H(\sigma)-\sum_xp(x)H(\rho_x)$, where $H(\rho)=-\operatorname{Tr}(\rho\log\rho)$ uses natural logarithms and $0\log0=0$. For every real $a<I(p)$ there is a single sequence of codes with $M_n\ge1$ distinct words in $\mathcal X^n$, and positive decoder effects summing to at most identity, such that
--
--   $$\liminf_{n\to\infty}\frac{\log M_n}{n}\ge a,\qquad \lim_{n\to\infty}P_e(C^n,X^n)=0.$$
--
--   Here the channel output for $x^n$ is $\rho_{x_1}\otimes\cdots\otimes\rho_{x_n}$ and $P_e$ is the error averaged over uniform messages, including the decoder's failure outcome. Rates are nats per use and $n\ge1$. This is the direct coding result for the chosen law $p$.
--
--   **Formalization Note** Positive lengths are indexed by $n=k+1$. The liminf bound is expressed equivalently by eventual rate bounds $a-\varepsilon$ for every $\varepsilon>0$.
-- source:
--   A New Proof of the Channel Coding Theorem via Hypothesis Testing in Quantum Information Theory, arXiv:quant-ph/0208139v1, PDF p. 5, (24)–(25)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P05

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P05

open scoped Matrix ComplexConjugate ComplexOrder BigOperators

open Filter Topology QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P07 (positiveProjection)

open QAlgorithms.Papers.Independent.Dependency50.P28 (tr pinch typeI accept)

open QAlgorithms.Papers.Independent.Claimed50.P45 (pinchedTest)

open QAlgorithms.Papers.Independent.Information100.P58 (Distribution)

open QAlgorithms.Papers.Independent.Information100.P27 (average)

open QAlgorithms.Papers.Independent.Dependency50.P07 (wordProb)

open QAlgorithms.Papers.Independent.Dependency50.P35 (directSum)

open QAlgorithms.Papers.Independent.Renew46.P44 (wordOutput)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {X I : Type} [Fintype X] [DecidableEq X] [Fintype I] [DecidableEq I]

/-- PDF p.5, (24)–(25), using the operational definitions on pp.1–2:
for every a < I(p), a SINGLE sequence of positive-length codes has vanishing
uniform-message average error and liminf rate at least a. The eventual lower
bounds for every positive eps express precisely liminf >= a without a real
conditional-infimum default. No converse or maximum-message error is asserted. -/
theorem cq_coding_direct (W : DensityOutputChannel X I) (p : Distribution X)
    (a : ℝ) (ha : a < channelInformationNats W p) :
    ∃ C : ∀ k : ℕ, DistinctWordCode (Fin (k + 1) → X) (Fin (k + 1) → I),
      (∀ eps : ℝ, 0 < eps → ∀ᶠ k : ℕ in atTop,
        a - eps ≤ Real.log ((C k).size : ℝ) / ((k + 1 : ℕ) : ℝ)) ∧
      Tendsto (fun k : ℕ => uniformMessageError (wordOutput W.state (n := k + 1)) (C k))
        atTop (𝓝 0) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P05

end
