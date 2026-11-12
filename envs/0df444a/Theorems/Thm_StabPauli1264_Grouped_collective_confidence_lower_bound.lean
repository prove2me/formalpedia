-- Prove2me | Theorems.Thm_StabPauli1264_Grouped_collective_confidence_lower_bound
-- name    : StabPauli1264.Grouped.collective_confidence_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T16:28:22.641431+00:00
-- url     : https://prove2.me/theorems/ef3f7c13-98fa-468c-97d0-adc8523be516
-- title:
--   §7 Eq. (31) — Collective confidence lower bound
-- statement:
--   Fix $0<\varepsilon_0,\delta_0<1/2$. Put $a=1+1/(2\varepsilon_0)$, $\bar\mu=\varepsilon_0+1/2$ and
--
--   $$A_{\delta_0}=(1-2\delta_0)\left(1+\frac{\ln(1-\delta_0)}{\ln(1/\delta_0)}\right),\qquad B_{\varepsilon_0,\delta_0}=\frac{(1-\bar\mu^2)A_{\delta_0}}{2a^2}>0.$$
--
--   For any nonempty window, choose any one observable $P_i$ and let $p$ concentrate on it. For $0<\varepsilon\le\varepsilon_0$, $0<\delta\le\delta_0$, the matrices $\rho_\pm=2^{-n}(I\pm a\varepsilon P_i)$ are physical stabilizer mixtures. Any $N$-copy collective procedure returning an arbitrary bounded real predictor $h\in[-1,1]^m$ and achieving excess risk at most $\varepsilon$ with probability at least $1-\delta$ on both targets satisfies
--
--   $$N\ge B_{\varepsilon_0,\delta_0}\frac{\ln(1/\delta)}{\varepsilon^2}.$$
--
--   The procedure is fixed before the target is chosen and may use arbitrary collective POVMs and measurable randomized postprocessing. No testing or relative-entropy inequality is assumed. This supplies the worst-evaluation-distribution confidence lower bound, including improper outputs.
--
--   Differences from the source:
--   - encoding: arbitrary measurement followed by a measurable bounded prediction → countably additive Borel POVM directly on the prediction cube; reason: pushing a POVM through all classical randomness and measurable postprocessing gives exactly this interface
--   - encoding: physical stabilizer-mixture hard targets → explicit density and convex-mixture conclusions for both literal matrices; reason: the physical content stated before Eq. (31) is proved rather than assumed
-- source:
--   Yingjian Liu, Xiaoyi Yang, Zhaohui Yang, STOC 2027 submission #1264 (October 2026), §7, Eqs. (25)–(31), pp. 16–17; displayed Eq. (31), p. 17; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1264.pdf

import Definitions.Def_StabPauli1264_Grouped_Complexity
set_option autoImplicit false

namespace StabPauli1264.Grouped

/-- Liu--Yang--Yang, Section 7 Eq.(31), pp.16--17, including physical targets. -/
theorem collective_confidence_lower_bound
    (ε₀ δ₀ : ℝ) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ < 1 / 2)
    (hδ₀ : 0 < δ₀) (hδ₀1 : δ₀ < 1 / 2) :
    0 < lowerConstant ε₀ δ₀ ∧
    ∀ {n m : ℕ} (M : Window n m) (i : Fin m)
      (ε δ : ℝ), 0 < ε → ε ≤ ε₀ → 0 < δ → δ ≤ δ₀ →
      (∀ b : Bool, ClonableQMASep.Main.IsDensity (hardTarget M i ε₀ ε b) ∧
        IsStabilizerMixture (hardTarget M i ε₀ ε b)) ∧
      ∀ (N : ℕ) (A : BoundedCollective n m N),
        (∀ b : Bool, 1 - δ ≤ boundedSuccess M (pointLaw i) A (hardTarget M i ε₀ ε b) ε) →
        lowerConstant ε₀ δ₀ * Real.log (1 / δ) / ε ^ 2 ≤ (N : ℝ) := by sorry

end StabPauli1264.Grouped
