-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P44_squeezed_process_fidelity
-- name    : QAlgorithms.Papers.Independent.Claimed50.P44.squeezed_process_fidelity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:08:01.731106+00:00
-- url     : https://prove2.me/theorems/ebbea14e-d4a8-4c50-be82-97cf37f4bdcf
-- title:
--   Squeezed-vacuum process score and coherent-input consequence
-- statement:
--   For $r\ge0$, take the physical centered two-mode squeezed vacuum with $A=B=\cosh(2r)I$ and $C=\operatorname{diag}(-\sinh(2r),\sinh(2r))$. Under the specified unity-gain Bell protocol,
--
--   $$\mathcal F(r)=e^{2r}.$$
--
--   The process score is strictly increasing on $[0,\infty)$. As an explicitly identified consequence of the pure-Gaussian fidelity formula, every coherent input has
--
--   $$F(r)=\frac{1}{1+e^{-2r}}.$$
--
--   Thus $F>1/2$ exactly when $r>0$, and $F>2/3$ exactly when $e^{-2r}<1/2$. At $r=0$ the process score is $1$ and coherent fidelity is $1/2$. These two quantities serve different operational purposes.
-- source:
--   Improving fidelity of continuous-variable teleportation via local operations, arXiv:quant-ph/0202102v3, PDF p. 3, §II, Eq.(22); §IV, Eq.(60), b0=0

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P44

noncomputable section

open MeasureTheory

open scoped Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Claimed50.P44

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify physicalCovariance pureCovariance)

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

/-- PDF p.3, Eq.(22), with correlation signs pinned by p.6, Eq.(60), b0=0.
The coherent-state clauses are identified algebraic consequences of (10), not
additional quotations. At r=0 the two distinct scores are 1 and 1/2. -/
theorem squeezed_process_fidelity (r : ℝ) (hr : 0 ≤ r) :
    let V := standardCov (Real.cosh (2 * r)) (Real.cosh (2 * r))
      (-Real.sinh (2 * r)) (Real.sinh (2 * r))
    let W := resourceWigner V 0
    PhysicalResource V ∧ processScore W = Real.exp (2 * r) ∧
    (∀ mean : PhasePoint, bellAverageFidelity 1 mean W = 1 / (1 + Real.exp (-2 * r))) ∧
    (∀ mean : PhasePoint, (1 / 2 < bellAverageFidelity 1 mean W ↔ 0 < r) ∧
      (2 / 3 < bellAverageFidelity 1 mean W ↔ Real.exp (-2 * r) < 1 / 2)) ∧
    StrictMonoOn (fun s : ℝ => processScore (resourceWigner
      (standardCov (Real.cosh (2 * s)) (Real.cosh (2 * s))
        (-Real.sinh (2 * s)) (Real.sinh (2 * s))) 0)) (Set.Ici 0) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P44

end
