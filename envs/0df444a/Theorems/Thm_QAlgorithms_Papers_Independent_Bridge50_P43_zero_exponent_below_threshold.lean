-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P43_zero_exponent_below_threshold
-- name    : QAlgorithms.Papers.Independent.Bridge50.P43.zero_exponent_below_threshold
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:21:59.810982+00:00
-- url     : https://prove2.me/theorems/6a1181e9-455e-4531-b1d7-19eb3500f834
-- title:
--   Zero strong-converse exponent at and below the threshold
-- statement:
--   All registers are nonzero finite-dimensional complex Hilbert spaces. States are positive operators of trace one, channels are completely positive and trace preserving, and logarithms are base two. Extended entropies retain $+\infty$.
--
--   Let $D=D(\mathcal N\|\mathcal R_\sigma)<+\infty$, and let $0<r\le D$. Use the adaptive errors, sequence exponents with strict type-II rate constraint, and finite-block optimum defined in Theorem 2. Then
--
--   $$
--   \underline{\mathrm{sc}}(r)=\overline{\mathrm{sc}}(r)=\lim_{n\to\infty}\frac{-\log_2(1-\alpha^{\mathrm{ad}}_{n,r})}{n}=\sup_{\alpha>1}\frac{\alpha-1}{\alpha}\bigl(r-\widetilde D_\alpha(\mathcal N\|\mathcal R_\sigma)\bigr)=0.
--   $$
--
--   This includes the threshold $r=D$. If $D=0$, the stipulated interval is empty. The remark completes the operational exponent description below the threshold.
-- source:
--   Strong converse exponents for a quantum channel discrimination problem and quantum-feedback-assisted communication, arXiv:1408.3373v3, PDF p. 8, Remark 3

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

/-- Remark 3, arXiv:1408.3373v3, PDF p.8.
Includes the boundary r=D; the interval is empty when D=0. -/
theorem zero_exponent_below_threshold
    {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Nonempty A] [Nonempty B] (N : Superop A B) (hN : IsChannel N)
    (sigma : NormalizedDensity B) (hfinite : channelDiv relativeD N (replacer sigma.1) < ⊤)
    (r : ℝ) (hr0 : 0 < r) (hr : (r : EReal) ≤ channelDiv relativeD N (replacer sigma.1)) :
    let M := replacer (A := A) sigma.1
    scLower r N M = 0 ∧ scUpper r N M = 0 ∧
    Tendsto (fun k : ℕ => positiveLengthExponent k (1 - optimalAlpha k r N M)) atTop (𝓝 0) ∧
    channelExponent r N M = 0 := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P43

end
