-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P89_integrated_brownian_rkhs
-- name    : QAlgorithms.Papers.Independent.Intake100.P89.integrated_brownian_rkhs
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:52:31.030757+00:00
-- url     : https://prove2.me/theorems/ebbfe6c7-9fbd-459e-927b-c81ec16c3c7e
-- title:
--   §10, unnumbered k-fold integrated Brownian motion
-- statement:
--   Let $W$ be continuous standard Brownian motion and $k\ge0$ an integer. The RKHS of its $k$-fold integral $I^kW$ is exactly $I^k(H_W)$, with the transported Brownian inner product. Equivalently it consists of $C^k$ functions whose $k$th derivative is absolutely continuous, whose $(k+1)$st derivative is in $L^2$, and whose initial derivatives of every order $0,\ldots,k$ vanish. In the exact integral parametrization,
--   $$H_{I^kW}=\{I^{k+1}f:f\in L^2[0,1]\},\qquad\langle I^{k+1}f,I^{k+1}g\rangle_H=\langle f,g\rangle_2.$$
--   For $k=0$ this is Brownian motion; for $k=1$ both $h(0)$ and $h'(0)$ vanish.
-- source:
--   Reproducing kernel Hilbert spaces of Gaussian priors, arXiv:0805.3252v1, PDF p. 20, §10, unnumbered k-fold integrated Brownian motion

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P89

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory

open scoped Topology BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Intake100.P89

universe u v w

variable {Omega : Type u} [MeasurableSpace Omega]

section PathResults

variable (P : Measure Omega) [hP : IsProbabilityMeasure P]

include hP

/-- §10, unnumbered k-fold integrated Brownian motion, arXiv:0805.3252v1, PDF p.20.
SOURCE CORRECTION: the later shorthand omits zero boundary derivatives. The preceding exact image I^k(H_W) forces all k+1 initial values, encoded by I^(k+1). No unrestricted Sobolev space is substituted. -/
theorem integrated_brownian_rkhs
(W : Omega → C(Time, ℝ)) (hW : StandardBrownian P W) (k : ℕ) :
    let X := fun t : Time => fun o => iterPrimitive k (W o) t
    processRKHS P X = Set.range (fun g : TimeL2 => iterPrimitive (k + 1) g) ∧
    processRKHS P X = iterPrimitive k '' processRKHS P (fun t o => W o t) ∧
    (∀ f g : TimeL2,
      processInner P X (iterPrimitive (k + 1) f) (iterPrimitive (k + 1) g) = inner ℝ f g) ∧
    ∀ g : TimeL2, iterPrimitive (k + 1) g ⟨0, by norm_num⟩ = 0 := by sorry

end PathResults

end QAlgorithms.Papers.Independent.Intake100.P89

end
