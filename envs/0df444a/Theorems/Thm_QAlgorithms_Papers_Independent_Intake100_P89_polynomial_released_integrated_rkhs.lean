-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P89_polynomial_released_integrated_rkhs
-- name    : QAlgorithms.Papers.Independent.Intake100.P89.polynomial_released_integrated_rkhs
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:53:01.744601+00:00
-- url     : https://prove2.me/theorems/e8cd552a-1b2f-4214-ba0b-911ab006a31d
-- title:
--   §10, unnumbered polynomial release of integrated Brownian derivatives
-- statement:
--   Let $W$ be continuous standard Brownian motion, $k\ge0$, and let $Z_0,\ldots,Z_k$ be iid standard normals jointly independent of $W$. Set $X_t=\sum_{i=0}^kZ_it^i/i!+(I^kW)_t$. Its RKHS is the full Sobolev class of $C^k$ functions with absolutely continuous $k$th derivative and square-integrable $(k+1)$st derivative, without zero boundary restrictions. Writing uniquely $h=P_a+I^{k+1}f$, $a_i=h^{(i)}(0)$, gives
--   $$\langle h,g\rangle_H=\sum_{i=0}^kh^{(i)}(0)g^{(i)}(0)+\int_0^1h^{(k+1)}(s)g^{(k+1)}(s)\,ds.$$
--   This equals the dot product of the initial jets plus the $L^2$ pairing of the last derivatives.
-- source:
--   Reproducing kernel Hilbert spaces of Gaussian priors, arXiv:0805.3252v1, PDF p. 20, §10, unnumbered polynomial release of integrated Brownian derivatives

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

/-- §10, unnumbered polynomial release of integrated Brownian derivatives, arXiv:0805.3252v1, PDF p.20.
The integral parametrization enforces exactly the Sobolev class. Source support separation is in C^k with ||f||infinity+||f^(k)||infinity, not C; independence and factorial normalization are retained. k=0 recovers released Brownian motion. -/
theorem polynomial_released_integrated_rkhs
(W : Omega → C(Time, ℝ)) (hW : StandardBrownian P W) (k : ℕ)
    (Z : Fin (k + 1) → Omega → ℝ) (hZ : StandardNormals P Z)
    (hind : Indep (MeasurableSpace.comap (fun o i => Z i o) inferInstance)
      (MeasurableSpace.comap W (borel C(Time, ℝ))) P) :
    let X := fun t : Time => fun o =>
      polynomialReal k (fun i => Z i o) (t : ℝ) + iterPrimitive k (W o) t
    processRKHS P X = {h | ∃ a : Fin (k + 1) → ℝ,
      ∃ f : TimeL2, h = sobolevPath k a f} ∧
    Function.Injective (fun af : (Fin (k + 1) → ℝ) × TimeL2 => sobolevPath k af.1 af.2) ∧
    ∀ (a b : Fin (k + 1) → ℝ) (f g : TimeL2),
      processInner P X (sobolevPath k a f) (sobolevPath k b g) =
        (∑ i, a i * b i) + inner ℝ f g := by sorry

end PathResults

end QAlgorithms.Papers.Independent.Intake100.P89

end
