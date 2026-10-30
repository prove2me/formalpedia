-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P43_operational_direct_and_strong_converse
-- name    : QAlgorithms.Papers.Independent.Bridge50.P43.operational_direct_and_strong_converse
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:29:04.187686+00:00
-- url     : https://prove2.me/theorems/258faf47-70d5-4d65-ab81-9a9911514dd1
-- title:
--   Direct and strong-converse operational formulations
-- statement:
--   All registers are nonzero finite-dimensional complex Hilbert spaces. States are positive operators of trace one, channels are completely positive and trace preserving, and logarithms are base two. Extended entropies retain $+\infty$.
--
--   Fix $\mathcal N$ and $\mathcal R_\sigma$. An adaptive strategy uses one common normalized initial state, common CPTP interleavings independent of the hypothesis, and one common binary effect. Write $p_n$ for acceptance under $\mathcal N$ and $q_n$ for acceptance under $\mathcal R_\sigma(X)=\operatorname{Tr}(X)\sigma$. Thus the type-I and type-II errors are $1-p_n$ and $q_n$, respectively. All optimizations are over actual strategies and arbitrary finite memories. For every real $r<D(\mathcal N\|\mathcal R_\sigma)$ there exists one sequence of adaptive strategies such that
--
--   $$
--   1-p_n\longrightarrow0,\qquad \liminf_{n\to\infty}\frac{-\log_2q_n}{n}\ge r.
--   $$
--
--   For every real $r>D(\mathcal N\|\mathcal R_\sigma)$, every adaptive sequence satisfying that same at-least-$r$ condition obeys
--
--   $$
--   1-p_n\longrightarrow1.
--   $$
--
--   These are the operational direct and strong-converse formulations, including extended relative entropy. Their rate constraint is non-strict, unlike the definition of the optimized strong-converse exponents.
-- source:
--   Strong converse exponents for a quantum channel discrimination problem and quantum-feedback-assisted communication, arXiv:1408.3373v3, PDF p. 20, Remark 14

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

/-- Remark 14, arXiv:1408.3373v3, PDF p.20.
The direct sequence is chosen before the block length; the converse is universal.
The type-II rate condition here is at least r, as opposed to (2.6)--(2.7). -/
theorem operational_direct_and_strong_converse
    {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Nonempty A] [Nonempty B] (N : Superop A B) (hN : IsChannel N) (sigma : NormalizedDensity B) :
    let M := replacer (A := A) sigma.1
    (∀ r : ℝ, (r : EReal) < channelDiv relativeD N M →
      ∃ P : StrategySequence A B,
        Tendsto (fun k => 1 - adaptiveAccept (P k) N) atTop (𝓝 0) ∧
        (r : EReal) ≤ Filter.liminf (fun k => positiveLengthExponent k (adaptiveAccept (P k) M)) atTop) ∧
    (∀ r : ℝ, channelDiv relativeD N M < (r : EReal) →
      ∀ P : StrategySequence A B,
        (r : EReal) ≤ Filter.liminf (fun k => positiveLengthExponent k (adaptiveAccept (P k) M)) atTop →
        Tendsto (fun k => 1 - adaptiveAccept (P k) N) atTop (𝓝 1)) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P43

end
