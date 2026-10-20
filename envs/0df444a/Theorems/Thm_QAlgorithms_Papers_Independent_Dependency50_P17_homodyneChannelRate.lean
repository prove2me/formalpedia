-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P17_homodyneChannelRate
-- name    : QAlgorithms.Papers.Independent.Dependency50.P17.homodyneChannelRate
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:50:15.801637+00:00
-- url     : https://prove2.me/theorems/cff0433b-3f2c-4d9d-b996-68ca623cc47a
-- title:
--   Homodyne channel and achievable mutual-information rate
-- statement:
--   Let $\alpha\in\mathbb C$, let $A,B$ be independent fair bits in $\mathbb F_2$, and let $Z$ be independent normal noise with mean zero and variance $1/4$. Aligned homodyne detection gives
--
--   $$
--   Y=\bigl((-1)^A+(-1)^B\bigr)|\alpha|+Z.
--   $$
--
--   Write $g_m(y)=\sqrt{2/\pi}\exp[-2(y-m)^2]$, $f_0=(g_{2|\alpha|}+g_{-2|\alpha|})/2$, $f_1=g_0$, and $f=(f_0+f_1)/2$. These are normalized densities with integrable entropy integrands. For $S=A+B$ in $\mathbb F_2$, the computation rate achievable by fixed single-use homodyne measurements and classical block processing is
--
--   $$
--   I(S;Y)=\frac12\sum_{s=0}^1\int_{\mathbb R} f_s(y)\log_2\frac{f_s(y)}{f(y)}\,dy
--   =h_{\rm diff}(f)-\frac12h_{\rm diff}(f_0)-\frac12h_{\rm diff}(f_1).
--   $$
--
--   Here $h_{\rm diff}(f_s)=-\int f_s\log_2 f_s$. Achievability means that there is a sequence of separate encoders and measurable classical decoders whose rates $\ell_n/n$ converge to this value and whose average sum-decoding error over independent uniform messages tends to zero. The measurement is fixed before the code sequence and messages. This is the source's application of the classical COMP results cited as [36]–[39].
--
--   **Formalization Note** The logarithm-dependent constant in the second line of printed (26) is not used.
-- source:
--   Computation-aided classical-quantum multiple access to boost network communication speeds, arXiv:2105.14505v1, PDF p. 10, §IV.D, (25), first line of (26)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P17

noncomputable section

open MeasureTheory

open scoped ENNReal BigOperators

namespace QAlgorithms.Papers.Independent.Dependency50.P17

open QAlgorithms.Papers.Independent.Information100.P56 (productOutput)

/-- PDF p.10, Section IV.D, (25) and the first line of (26): the homodyne
channel has variance-1/4 independent Gaussian noise and achieves I(A+B;Y).
All logarithms here are base two. Normalization and integrability clauses ensure
that the displayed differential entropies are actual expectations. Achievability
uses the classical COMP theory cited as [36]–[39] in this source, not a new
classical coding theorem attributed to this paper. The erroneous final constant
of the second line of (26) is not asserted. -/
theorem homodyneChannelRate (alpha : ℂ) :
    (∀ a b : ZMod 2,
      Integrable (homodyneSingle alpha a b) ∧
        (∫ y : ℝ, homodyneSingle alpha a b y) = 1) ∧
    (∀ s : ZMod 2,
      Integrable (homodyneSumDensity alpha s) ∧
        (∫ y : ℝ, homodyneSumDensity alpha s y) = 1 ∧
        Integrable (fun y => homodyneSumDensity alpha s y *
          Real.logb 2 (homodyneSumDensity alpha s y))) ∧
    (Integrable (homodyneMeanDensity alpha) ∧
      (∫ y : ℝ, homodyneMeanDensity alpha y) = 1 ∧
      Integrable (fun y => homodyneMeanDensity alpha y *
        Real.logb 2 (homodyneMeanDensity alpha y))) ∧
    homodyneRate alpha =
      -(∫ y : ℝ, homodyneMeanDensity alpha y * Real.logb 2 (homodyneMeanDensity alpha y)) +
        (∫ y : ℝ, homodyneSumDensity alpha 0 y * Real.logb 2 (homodyneSumDensity alpha 0 y)) / 2 +
        (∫ y : ℝ, homodyneSumDensity alpha 1 y * Real.logb 2 (homodyneSumDensity alpha 1 y)) / 2 ∧
    HomodyneAchievable alpha (homodyneRate alpha) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P17

end
