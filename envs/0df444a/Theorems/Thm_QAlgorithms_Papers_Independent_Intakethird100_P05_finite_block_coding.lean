-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P05_finite_block_coding
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P05.finite_block_coding
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T03:58:50.729528+00:00
-- url     : https://prove2.me/theorems/cfce95f4-fe94-4213-a3cc-e6c7ebb8f69f
-- title:
--   Finite-block iid channel coding bounds
-- statement:
--   For a density-output channel $x\mapsto\rho_x$ with finite input alphabet and finite-dimensional output space, fix any input law $p$ and let $\sigma=\sum_xp(x)\rho_x$. Set $\rho_{x^n}=\bigotimes_t\rho_{x_t}$, $p^n(x^n)=\prod_tp(x_t)$, and $\bar\rho_{x^n}=\mathcal E_{\sigma^{\otimes n}}(\rho_{x^n})$. For real $a$ define
--
--   $$\delta_n(a)=\sum_{x^n}p^n(x^n)\operatorname{Tr}[\bar\rho_{x^n}\{\bar\rho_{x^n}-e^{na}\sigma^{\otimes n}\le0\}].$$
--
--   For every integer $n\ge1$, every real $a$, every $\lambda>0$, and every $\gamma_n>0$, there is one code of $M_n\ge1$ distinct words with positive decoder effects summing to at most identity, satisfying
--
--   $$\frac{\gamma_n}{\gamma_n+\delta_n(a)}\min\{e^{-n\lambda},1-\delta_n(a)-\gamma_n-2\sqrt{e^{-n\lambda}}\}\le e^{-na}M_n,$$
--   $$P_e(C^n,X^n)\le\delta_n(a)+\gamma_n+2\sqrt{e^{-n\lambda}}.$$
--
--   Here $P_e$ is uniform-message average error on the original memoryless output states. This is a finite-block estimate; no mutual-information threshold or convergence assumption is required.
-- source:
--   A New Proof of the Channel Coding Theorem via Hypothesis Testing in Quantum Information Theory, arXiv:quant-ph/0208139v1, PDF p. 5, Theorem 1, (21)–(23)

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

/-- PDF p.5, Theorem 1, (21)–(23), with substitutions (20) on p.4:
for every positive length and gamma, and every lambda > 0, a code satisfies
the two finite-block bounds. No a < I(p) or convergence premise is imposed. -/
theorem finite_block_coding (W : DensityOutputChannel X I) (p : Distribution X)
    (n : ℕ) (hn : 1 ≤ n) (a lambda gamma : ℝ)
    (hlambda : 0 < lambda) (hgamma : 0 < gamma) :
    ∃ C : DistinctWordCode (Fin n → X) (Fin n → I),
      gamma / (gamma + pinchedLowerTail W p n a) *
        min (Real.exp (-(n : ℝ) * lambda))
          (1 - pinchedLowerTail W p n a - gamma -
            2 * Real.sqrt (Real.exp (-(n : ℝ) * lambda))) ≤
        Real.exp (-(n : ℝ) * a) * (C.size : ℝ) ∧
      uniformMessageError (wordOutput W.state (n := n)) C ≤ pinchedLowerTail W p n a + gamma +
        2 * Real.sqrt (Real.exp (-(n : ℝ) * lambda)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P05

end
