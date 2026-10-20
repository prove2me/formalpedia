-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P12_thermalEntropy_difference_asymptotics
-- name    : QAlgorithms.Papers.Independent.Frontier18.P12.thermalEntropy_difference_asymptotics
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T15:51:42.827989+00:00
-- url     : https://prove2.me/theorems/856983cb-a75a-4ccf-a75d-c21dee8ebeb5
-- title:
--   Thermal-entropy difference: monotonicity and finite or infinite limit
-- statement:
--   Let $g(x)=(x+1)\log_2(x+1)-x\log_2x$ for $x\ge0$, with $0\log_2 0=0$. For $\lambda\in[0,1]$, put $D_\lambda(x)=g(x)-g(\lambda x)$. Then $D_\lambda$ is nondecreasing on $[0,\infty)$ and
--
--   $$
--   \lim_{x\to\infty}D_\lambda(x)=\begin{cases}
--   \log_2(1/\lambda),&0<\lambda\le1,\\
--   +\infty,&\lambda=0.
--   \end{cases}
--   $$
--
--   This fact permits thermal bounds at finite energy to be replaced by bounds independent of energy. At $\lambda=1$ the difference is identically zero.
--
--   **Formalization Note** The printed real logarithm is undefined at the allowed endpoint $\lambda=0$. That endpoint is expressed as divergence to positive infinity. This source interpretation requires independent moderation.
-- source:
--   Bounds on entanglement distillation and secret key agreement for quantum broadcast channels, arXiv:1503.08139v2, PDF p. 28, §7, paragraph containing (7.18)

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P12

noncomputable section

namespace QAlgorithms.Papers.Independent.Frontier18.P12

open Filter

open QAlgorithms.Papers.Independent.Information100.P54 (thermalEntropy)

open scoped Topology

/-- Monotonic thermal-entropy difference and its limit, arXiv:1503.08139v2,
PDF p.28, the paragraph preceding and including (7.18). Both monotonicity and the
limit are included, for every lambda in [0,1].
Printed: a real `log(1/lambda)` limit also at lambda = 0. Changed: retain that
finite base-2 limit for positive lambda, and state divergence to positive infinity
at lambda = 0. Why: the printed real expression is undefined there, whereas
`g(x) - g(0)` diverges; Lean's division-by-zero default must not replace it.
At lambda = 1 the function is constant, so “increasing” means nondecreasing.
Independent moderation of the endpoint interpretation remains pending. -/
theorem thermalEntropy_difference_asymptotics (lambda : ℝ)
    (hlower : 0 ≤ lambda) (hupper : lambda ≤ 1) :
    MonotoneOn (fun x : ℝ => thermalEntropy x - thermalEntropy (lambda * x))
      (Set.Ici 0) ∧
    (0 < lambda →
      Tendsto (fun x : ℝ => thermalEntropy x - thermalEntropy (lambda * x))
        atTop (𝓝 (Real.logb 2 (1 / lambda)))) ∧
    (lambda = 0 →
      Tendsto (fun x : ℝ => thermalEntropy x - thermalEntropy (lambda * x))
        atTop atTop) := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P12

end
