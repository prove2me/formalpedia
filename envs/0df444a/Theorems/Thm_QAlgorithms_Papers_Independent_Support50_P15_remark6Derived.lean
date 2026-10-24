-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P15_remark6Derived
-- name    : QAlgorithms.Papers.Independent.Support50.P15.remark6Derived
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:39:24.393892+00:00
-- url     : https://prove2.me/theorems/049145d6-e735-43a4-a19e-b92aee768890
-- title:
--   remark6 derived
-- statement:
--   Let $d\ge2$, let $\sigma,\rho$ be normalized density matrices, set $x=|S(\sigma)-S(\rho)|$ and let $T=\|\sigma-\rho\|_1/2$. Write $h_d(u)=u\log(d-1)+H(u)$, where $H$ is binary entropy, and take its inverse on $[0,(d-1)/d]$. Define $b_d(0)=0$ and, for $x>0$, $b_d(x)=((e-1)/e)x/(1+\log(d-1)-\log x)$. Then
--
--   $$T\ge h_d^{-1}(x)\ge b_d(x),\qquad D(\sigma\|\rho)\ge2[h_d^{-1}(x)]^2\ge2b_d(x)^2.$$
--
--   The inverse satisfies $h_d(h_d^{-1}(x))=x$ on $[0,\log d]$ and $h_d^{-1}(x)/x\to0$ as $x\downarrow0$. In particular no positive constant $c(d)$ bounds this inverse below by $c(d)x$ throughout that interval. These are the derived inversion consequences; the cited Fannes--Audenaert and Pinsker theorems are background.
-- source:
--   Tight bound on relative entropy by entropy difference, arXiv:1304.0036v3, PDF p. 6, remark6-derived

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P15

noncomputable section

attribute [local instance] Classical.propDecidable

open scoped Matrix ComplexConjugate ENNReal Matrix.Norms.L2Operator

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Support50.P15

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

/-- Remark 6, Eq. (18), PDF p.6: derived inverse estimate, its relative-entropy consequences,
and the failure of a linear inverse bound near zero. Cited inequalities (16),(17) are background. -/
theorem remark6Derived (d : ℕ) (hd : 2 ≤ d) :
    (∀ a b : EntropyState d, let x := |difference a.val b.val|
      entropyInverse d x ≤ traceNorm (a.val - b.val) / 2 ∧
      inverseEstimate d x ≤ entropyInverse d x ∧
      (2 * (entropyInverse d x) ^ 2 : ℝ) ≤ stateRelativeNats a b ∧
      (2 * (inverseEstimate d x) ^ 2 : ℝ) ≤ stateRelativeNats a b) ∧
    (¬ ∃ c : ℝ, 0 < c ∧ ∀ x ∈ Set.Icc (0 : ℝ) (Real.log d), c * x ≤ entropyInverse d x) ∧
    (∀ x ∈ Set.Icc (0 : ℝ) (Real.log d), continuityEntropy d (entropyInverse d x) = x) ∧
    Tendsto (fun x : ℝ => entropyInverse d x / x) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by sorry

end QAlgorithms.Papers.Independent.Support50.P15

end
