-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P28_wiretap_rates_and_exponent
-- name    : QAlgorithms.Papers.Independent.Advance50.P28.wiretap_rates_and_exponent
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:54:44.707704+00:00
-- url     : https://prove2.me/theorems/b9a709a6-afd1-4f0b-8332-99eed0a76263
-- title:
--   Wiretap achievable rate and secrecy exponent
-- statement:
--   Let $W^B:X\to\operatorname{Prob}(Y)$ and $W^E:X\to\operatorname{Prob}(Z)$ be classical stochastic channels with countable discrete input and measurable output densities, and let $p$ be an input law. Put $J_t(W,p)=\int(\sum_xp(x)W_x(y)^{1/(1-t)})^{1-t}\,dy=\exp\phi(t\mid W,p)$. Codes have normalized stochastic encoders, disjoint measurable decoding sets, uniform messages, average Bob error $\epsilon_B$, and full $L^1$ message–Eve dependence $d_1$ against their actual Eve marginal. Let $I_B=I(p:W^B)$ and $I_E=I(p:W^E)$ be relative-entropy mutual informations in nats, allowing $+\infty$. If finite nonnegative real numbers $r,R$ satisfy $I_E\le R$ and $r+R\le I_B$, there are codes $\Phi_n$ with positive message sizes $M_n$ such that
--   $$\frac{\log M_n}n\longrightarrow r,\quad\epsilon_B(\Phi_n)\longrightarrow0,\quad d_1(\Phi_n|E)\longrightarrow0,\quad\liminf_n-\frac1n\log d_1(\Phi_n|E)\ge\sup_{0\le t\le1/2}\{tR-\phi(t|W^E,p)\}.$$
--   Boundary rates mean limits of operating rates from below, without a positive reliability-exponent claim. Quantification over all input laws gives rates approaching their information-difference supremum, without asserting an input-law maximizer.
-- source:
--   Tight exponential analysis of universally composable privacy amplification and its applications, arXiv:1010.1358v5, PDF p. 13, Wiretap achievable rate and secrecy exponent

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P28

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology

namespace QAlgorithms.Papers.Independent.Advance50.P28

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Hayashi, PDF p.13: achievable rates up to the information difference, with
secrecy exponent at the chosen sacrifice rate. Universal quantification over p
allows optimization without inventing a maximizing distribution. Closed-rate
endpoints mean limits of operating rates from below, not positive reliability exponents. -/
theorem wiretap_rates_and_exponent {X Y E : Type*} [Countable X] [Nonempty X]
    [MeasurableSpace Y] [MeasurableSpace E]
    (muB : Measure Y) (muE : Measure E) [SigmaFinite muB] [SigmaFinite muE]
    (WB : X → Y → ℝ≥0∞) (WE : X → E → ℝ≥0∞)
    (hB : IsDensityChannel muB WB) (hE : IsDensityChannel muE WE)
    (p : X → ℝ≥0∞) (hp : IsENNRealDiscreteLaw p) (r R : ℝ) (hr : 0 ≤ r)
    (hR : 0 ≤ R) (hEinfo : classicalMutualInformationNats muE WE p ≤ ENNReal.ofReal R)
    (hBinfo : ENNReal.ofReal (r + R) ≤ classicalMutualInformationNats muB WB p) :
    ∃ M : ℕ → ℕ, (∀ n, 0 < M n) ∧
      ∃ C : (n : ℕ) → WiretapCode (Fin n → X) (Fin n → Y) (M n),
        Tendsto (fun n => Real.log (M n : ℝ) / (n : ℝ)) atTop (𝓝 r) ∧
        Tendsto (fun n => wiretapDecodingError (Measure.pi (fun _ : Fin n => muB))
          (blockDensity WB n) (C n)) atTop (𝓝 0) ∧
        Tendsto (fun n => codeLeakage (Measure.pi (fun _ : Fin n => muE))
          (blockDensity WE n) (C n)) atTop (𝓝 0) ∧
        wiretapPhiExponent muE WE p R ≤ Filter.liminf (fun n => negativeLogRateENN
          (codeLeakage (Measure.pi (fun _ : Fin n => muE)) (blockDensity WE n) (C n)) n)
          atTop := by sorry

end QAlgorithms.Papers.Independent.Advance50.P28

end
