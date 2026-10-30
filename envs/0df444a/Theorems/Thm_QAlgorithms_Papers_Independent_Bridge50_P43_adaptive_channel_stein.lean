-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P43_adaptive_channel_stein
-- name    : QAlgorithms.Papers.Independent.Bridge50.P43.adaptive_channel_stein
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:20:09.657068+00:00
-- url     : https://prove2.me/theorems/855d6c8e-7a2f-4a65-9df7-6076d8f370df
-- title:
--   Adaptive channel Stein lemma
-- statement:
--   All registers are nonzero finite-dimensional complex Hilbert spaces. States are positive operators of trace one, channels are completely positive and trace preserving, and logarithms are base two. Extended entropies retain $+\infty$.
--
--   Let $\mathcal N:A\to B$ be a channel, let $\sigma$ be a state on $B$, and fix $0<\varepsilon<1$. An adaptive strategy uses one common normalized initial state, common CPTP interleavings independent of the hypothesis, and one common binary effect. Write $p_n$ for acceptance under $\mathcal N$ and $q_n$ for acceptance under $\mathcal R_\sigma(X)=\operatorname{Tr}(X)\sigma$. Thus the type-I and type-II errors are $1-p_n$ and $q_n$, respectively. All optimizations are over actual strategies and arbitrary finite memories. Let $\beta^{\mathrm{ad}}_\varepsilon(n)$ be the infimum of $q_n$ subject to $p_n\ge1-\varepsilon$, and let $D^{\varepsilon}_{H,\mathrm{ad}}(n)=-\log_2\beta^{\mathrm{ad}}_\varepsilon(n)$. Then
--
--   $$
--   \lim_{n\to\infty}\frac{-\log_2\beta^{\mathrm{ad}}_\varepsilon(n)}{n}=\lim_{n\to\infty}\frac{D^{\varepsilon}_{H,\mathrm{ad}}(n)}{n}=D(\mathcal N\|\mathcal R_\sigma)=\sup_{R,\psi_{RA}}D((\mathrm{id}_R\otimes\mathcal N)(\psi_{RA})\|\psi_R\otimes\sigma).
--   $$
--
--   The supremum initially ranges over all finite references and all mixed input states. It has the same value when $R$ is a fixed copy of $A$. The limit is extended-valued, including zero optimal type-II error. This identifies the optimal adaptive testing rate.
-- source:
--   Strong converse exponents for a quantum channel discrimination problem and quantum-feedback-assisted communication, arXiv:1408.3373v3, PDF p. 6, Theorem 1, (2.4)–(2.5)

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

/-- Theorem 1, arXiv:1408.3373v3, PDF pp.6--7, (2.4)--(2.5).
No full-rank or finite-relative-entropy assumption. Fixed-reference reduction is a conclusion. -/
theorem adaptive_channel_stein
    {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Nonempty A] [Nonempty B] (N : Superop A B) (hN : IsChannel N)
    (sigma : NormalizedDensity B) (epsilon : ℝ) (he0 : 0 < epsilon) (he1 : epsilon < 1) :
    Tendsto (fun k : ℕ => positiveLengthExponent k (adaptiveBeta (k+1) epsilon N (replacer sigma.1)))
      atTop (𝓝 (channelDiv relativeD N (replacer sigma.1))) ∧
    Tendsto (fun k : ℕ => (((1 : ℝ)/(k+1 : ℕ) : ℝ) : EReal) *
      adaptiveTestingD k epsilon N (replacer sigma.1))
      atTop (𝓝 (channelDiv relativeD N (replacer sigma.1))) ∧
    channelDiv relativeD N (replacer sigma.1) = fixedMixedDiv relativeD N (replacer sigma.1) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P43

end
