-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P43_uniform_adaptive_renyi_bound
-- name    : QAlgorithms.Papers.Independent.Bridge50.P43.uniform_adaptive_renyi_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:29:56.567689+00:00
-- url     : https://prove2.me/theorems/0802387a-8562-425a-b770-1763b4075416
-- title:
--   Uniform finite-use adaptive Renyi and testing bounds
-- statement:
--   All registers are nonzero finite-dimensional complex Hilbert spaces. States are positive operators of trace one, channels are completely positive and trace preserving, and logarithms are base two. Extended entropies retain $+\infty$.
--
--   Fix a channel $\mathcal N$, a replacer $\mathcal R_\sigma$, an integer $n\ge1$, an order $\alpha>1$, and $0<\varepsilon<1$. An adaptive strategy uses one common normalized initial state, common CPTP interleavings independent of the hypothesis, and one common binary effect. Write $p_n$ for acceptance under $\mathcal N$ and $q_n$ for acceptance under $\mathcal R_\sigma(X)=\operatorname{Tr}(X)\sigma$. Thus the type-I and type-II errors are $1-p_n$ and $q_n$, respectively. All optimizations are over actual strategies and arbitrary finite memories. Let $\rho_n$ and $\tau_n$ be the two premeasurement terminal states computed by one such strategy, and let $D^{\varepsilon}_{H,\mathrm{ad}}(n)$ optimize the testing divergence over all such strategies. Then
--
--   $$
--   \widetilde D_\alpha(\rho_n\|\tau_n)\le n\widetilde D_\alpha(\mathcal N\|\mathcal R_\sigma),\qquad \frac1nD^{\varepsilon}_{H,\mathrm{ad}}(n)\le\widetilde D_\alpha(\mathcal N\|\mathcal R_\sigma)+\frac{\alpha}{n(\alpha-1)}\log_2\frac1{1-\varepsilon}.
--   $$
--
--   The first inequality holds for every actual adaptive strategy and the second is its optimized testing consequence. Both remain meaningful at infinite channel divergence. These are the common quantitative bounds behind the main adaptive results.
-- source:
--   Strong converse exponents for a quantum channel discrimination problem and quantum-feedback-assisted communication, arXiv:1408.3373v3, PDF p. 17, Unnumbered (4.16)–(4.17)

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

/-- Central bounds (4.16)--(4.17), arXiv:1408.3373v3, PDF pp.15--17.
Every terminal pair is computed by the same strategy under the two fixed channels.
The uniform channel bound and optimized testing inequality are conclusions. -/
theorem uniform_adaptive_renyi_bound
    {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Nonempty A] [Nonempty B] (N : Superop A B) (hN : IsChannel N)
    (sigma : NormalizedDensity B) (k : ℕ) (alpha : ℝ) (ha : 1 < alpha)
    (epsilon : ℝ) (he0 : 0 < epsilon) (he1 : epsilon < 1) :
    let M := replacer (A := A) sigma.1
    (∀ P : AdaptiveTest A B (k+1),
      sandwichedWithUmegaki alpha (adaptiveTerminalState P N) (adaptiveTerminalState P M) ≤
        (((k+1 : ℕ) : ℝ) : EReal) * channelDiv (sandwichedWithUmegaki alpha) N M) ∧
    (((1 : ℝ)/(k+1 : ℕ) : ℝ) : EReal) * adaptiveTestingD k epsilon N M ≤
      channelDiv (sandwichedWithUmegaki alpha) N M +
        (((alpha / (((k+1 : ℕ) : ℝ) * (alpha-1)) : ℝ) : EReal) * surprisal (1-epsilon)) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P43

end
