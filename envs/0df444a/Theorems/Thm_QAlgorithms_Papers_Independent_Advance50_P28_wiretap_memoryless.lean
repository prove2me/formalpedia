-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P28_wiretap_memoryless
-- name    : QAlgorithms.Papers.Independent.Advance50.P28.wiretap_memoryless
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:54:07.022375+00:00
-- url     : https://prove2.me/theorems/8cf2abc2-8cb8-40d1-8498-9865945452ec
-- title:
--   Memoryless wiretap code bounds
-- statement:
--   Let $W^B:X\to\operatorname{Prob}(Y)$ and $W^E:X\to\operatorname{Prob}(Z)$ be classical stochastic channels with countable discrete input and measurable output densities, and let $p$ be an input law. Put $J_t(W,p)=\int(\sum_xp(x)W_x(y)^{1/(1-t)})^{1-t}\,dy=\exp\phi(t\mid W,p)$. Codes have normalized stochastic encoders, disjoint measurable decoding sets, uniform messages, average Bob error $\epsilon_B$, and full $L^1$ message–Eve dependence $d_1$ against their actual Eve marginal. For $n,M,L\ge1$, a single code on the actual product channels has $M$ messages and
--   $$\epsilon_B\le3\inf_{0\le t\le1}(ML)^tJ_{-t}(W^B,p)^n,\qquad d_1\le9\inf_{0\le t\le1/2}\frac{J_t(W^E,p)^n}{L^t}.$$
--   Only the random-coding input is $p^n$; the selected stochastic encoders may correlate all channel uses. A sigma-finite reference output measure is used for the tensor products; a countable channel family always admits a dominating probability reference measure.
-- source:
--   Tight exponential analysis of universally composable privacy amplification and its applications, arXiv:1010.1358v5, PDF p. 13, Memoryless wiretap code bounds

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P28

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology

namespace QAlgorithms.Papers.Independent.Advance50.P28

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Hayashi, PDF p.13: memoryless code bounds use p^n and actual product channels;
encoders may correlate all n channel inputs. -/
theorem wiretap_memoryless {X Y E : Type*} [Countable X] [Nonempty X]
    [MeasurableSpace Y] [MeasurableSpace E]
    (muB : Measure Y) (muE : Measure E) [SigmaFinite muB] [SigmaFinite muE]
    (WB : X → Y → ℝ≥0∞) (WE : X → E → ℝ≥0∞)
    (hB : IsDensityChannel muB WB) (hE : IsDensityChannel muE WE)
    (p : X → ℝ≥0∞) (hp : IsENNRealDiscreteLaw p)
    (n M L : ℕ) (hn : 0 < n) (hM : 0 < M) (hL : 0 < L) :
    ∃ C : WiretapCode (Fin n → X) (Fin n → Y) M,
      wiretapDecodingError (Measure.pi (fun _ : Fin n => muB)) (blockDensity WB n) C ≤
        3 * sInf ((fun t : ℝ => (M * L : ℝ≥0∞) ^ t *
          (gallagerDensityMoment muB WB p (-t)) ^ n) '' Set.Icc 0 1) ∧
      codeLeakage (Measure.pi (fun _ : Fin n => muE)) (blockDensity WE n) C ≤
        9 * sInf ((fun t : ℝ => (gallagerDensityMoment muE WE p t) ^ n /
          (L : ℝ≥0∞) ^ t) '' Set.Icc 0 (1 / 2)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P28

end
