-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P43_testing_vs_sandwiched
-- name    : QAlgorithms.Papers.Independent.Bridge50.P43.testing_vs_sandwiched
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:22:44.5937+00:00
-- url     : https://prove2.me/theorems/b2ff93b6-9b4c-48e8-ab2b-ccaf55fd7a13
-- title:
--   Testing bounds from sandwiched Renyi divergence
-- statement:
--   All registers are nonzero finite-dimensional complex Hilbert spaces. States are positive operators of trace one, channels are completely positive and trace preserving, and logarithms are base two. Extended entropies retain $+\infty$.
--
--   Let $\rho,\sigma$ be states with $\operatorname{supp}\rho\subseteq\operatorname{supp}\sigma$, and let $\alpha>1$. Write $s(p)=-\log_2p$, with $s(0)=+\infty$. For every effect $0\le Q\le I$ and every $0<\varepsilon<1$,
--
--   $$
--   s(\operatorname{Tr}Q\sigma)\le\widetilde D_\alpha(\rho\|\sigma)+\frac{\alpha}{\alpha-1}s(\operatorname{Tr}Q\rho),\qquad D_H^\varepsilon(\rho\|\sigma)\le\widetilde D_\alpha(\rho\|\sigma)+\frac{\alpha}{\alpha-1}\log_2\frac1{1-\varepsilon}.
--   $$
--
--   Here $D_H^\varepsilon$ is minus the logarithm of the infimum of type-II acceptance over effects with null acceptance at least $1-\varepsilon$. At $Q=0$ the first inequality reads $+\infty\le+\infty$. These bounds relate testing constraints to Renyi information.
-- source:
--   Strong converse exponents for a quantum channel discrimination problem and quantum-feedback-assisted communication, arXiv:1408.3373v3, PDF p. 11, Lemma 5, (3.7)–(3.8)

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P43

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology

open Filter

namespace QAlgorithms.Papers.Independent.Bridge50.P43

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P09 (Divergence relativeD petzD sandwichedD)

open QAlgorithms.Papers.Independent.Information100.P71
  (SupportIncluded supportPower AdaptiveTest adaptiveInput adaptiveAccept adaptiveBeta channelPower)

open QAlgorithms.Papers.Independent.Information100.P58 (testingD)
-- Exactly the trace-preparation map of PDF pp.5--6, on every operator.

open QAlgorithms.Papers.Independent.Information100.P69 (replacer)

/-- Lemma 5, arXiv:1408.3373v3, PDF pp.11--12, (3.7)--(3.8).
At zero acceptance, both sides are positive infinity; addition of nonnegative
extended surprisals avoids the indeterminate subtraction of infinite logarithms. -/
theorem testing_vs_sandwiched
    {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (rho sigma : NormalizedDensity I) (hsupport : SupportIncluded rho.1 sigma.1)
    (alpha : ℝ) (ha : 1 < alpha) :
    (∀ Q : Matrix I I ℂ, IsEffect Q →
      surprisal (effectProb Q sigma.1) ≤ sandwichedWithUmegaki alpha rho.1 sigma.1 +
        (((alpha/(alpha-1) : ℝ) : EReal) * surprisal (effectProb Q rho.1))) ∧
    (∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 →
      testingD epsilon rho.1 sigma.1 ≤ sandwichedWithUmegaki alpha rho.1 sigma.1 +
        (((alpha/(alpha-1) : ℝ) : EReal) * surprisal (1-epsilon))) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P43

end
