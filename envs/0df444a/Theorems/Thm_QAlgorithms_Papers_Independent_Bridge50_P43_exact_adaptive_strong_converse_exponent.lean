-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P43_exact_adaptive_strong_converse_exponent
-- name    : QAlgorithms.Papers.Independent.Bridge50.P43.exact_adaptive_strong_converse_exponent
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:21:09.66693+00:00
-- url     : https://prove2.me/theorems/3ce7f12c-9e50-4c87-94ef-ebd42954a868
-- title:
--   Exact adaptive strong-converse exponent
-- statement:
--   All registers are nonzero finite-dimensional complex Hilbert spaces. States are positive operators of trace one, channels are completely positive and trace preserving, and logarithms are base two. Extended entropies retain $+\infty$.
--
--   Fix a channel $\mathcal N$ and replacer $\mathcal R_\sigma$, and a real rate $r>D(\mathcal N\|\mathcal R_\sigma)$. An adaptive strategy uses one common normalized initial state, common CPTP interleavings independent of the hypothesis, and one common binary effect. Write $p_n$ for acceptance under $\mathcal N$ and $q_n$ for acceptance under $\mathcal R_\sigma(X)=\operatorname{Tr}(X)\sigma$. Thus the type-I and type-II errors are $1-p_n$ and $q_n$, respectively. All optimizations are over actual strategies and arbitrary finite memories. Let $\alpha^{\mathrm{ad}}_{n,r}=\inf\{1-p_n:q_n\le2^{-nr}\}$. Define $\underline{\mathrm{sc}}(r)$ and $\overline{\mathrm{sc}}(r)$ as the infima, over strategy sequences satisfying $\liminf_n-n^{-1}\log_2q_n>r$, of $\liminf_n-n^{-1}\log_2p_n$ and $\limsup_n-n^{-1}\log_2p_n$, respectively. For an input $\psi_{RA}$ put $d_\alpha(\psi)=\widetilde D_\alpha((\mathrm{id}_R\otimes\mathcal N)(\psi)\|\psi_R\otimes\sigma)$. Then
--
--   $$
--   \begin{aligned}
--   \underline{\mathrm{sc}}(r)=\overline{\mathrm{sc}}(r)&=\lim_{n\to\infty}\frac{-\log_2(1-\alpha^{\mathrm{ad}}_{n,r})}{n}\\
--   &=\sup_{\alpha>1}\inf_{R,\psi}\frac{\alpha-1}{\alpha}(r-d_\alpha(\psi))\\
--   &=\inf_{R,\psi}\sup_{\alpha>1}\frac{\alpha-1}{\alpha}(r-d_\alpha(\psi))\\
--   &=\sup_{\alpha>1}\frac{\alpha-1}{\alpha}(r-\widetilde D_\alpha(\mathcal N\|\mathcal R_\sigma)).
--   \end{aligned}
--   $$
--
--   Both infima have the same values if restricted to pure inputs with a fixed reference copy of $A$. This gives the exact exponential loss of acceptance in the strong-converse regime.
-- source:
--   Strong converse exponents for a quantum channel discrimination problem and quantum-feedback-assisted communication, arXiv:1408.3373v3, PDF p. 7, Theorem 2, (2.9)–(2.12)

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

/-- Theorem 2, arXiv:1408.3373v3, PDF pp.7--8, (2.9)--(2.12).
Both sequence exponents, the finite-block limit, both minimax orders, and both
fixed-copy pure-input restrictions are retained. -/
theorem exact_adaptive_strong_converse_exponent
    {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Nonempty A] [Nonempty B] (N : Superop A B) (hN : IsChannel N)
    (sigma : NormalizedDensity B) (r : ℝ) (hr : channelDiv relativeD N (replacer sigma.1) < (r : EReal)) :
    let M := replacer (A := A) sigma.1
    let V := channelExponent r N M
    scLower r N M = V ∧ scUpper r N M = V ∧
    Tendsto (fun k : ℕ => positiveLengthExponent k (1 - optimalAlpha k r N M)) atTop (𝓝 V) ∧
    (⨆ alpha : {a : ℝ // 1 < a}, ⨅ psi : FiniteReferenceInput A, inputPayoff alpha.1 r N M psi) = V ∧
    (⨅ psi : FiniteReferenceInput A, ⨆ alpha : {a : ℝ // 1 < a}, inputPayoff alpha.1 r N M psi) = V ∧
    (⨆ alpha : {a : ℝ // 1 < a}, ⨅ psi : UnitStateVector (A × A), purePayoff alpha.1 r N M psi) = V ∧
    (⨅ psi : UnitStateVector (A × A), ⨆ alpha : {a : ℝ // 1 < a}, purePayoff alpha.1 r N M psi) = V := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P43

end
