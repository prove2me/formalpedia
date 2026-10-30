-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P22_approximate_eastin_knill
-- name    : QAlgorithms.Papers.Independent.Extend50.P22.approximate_eastin_knill
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:14:13.192667+00:00
-- url     : https://prove2.me/theorems/2324ffb1-f947-48b2-a25d-ff1f0d7fe239
-- title:
--   Theorem 4: Approximate Eastin-Knill theorem, Eqs.(51)–(52)
-- statement:
--   Let an isometry $V:L\to\bigotimes_{i=1}^n A_i$ encode a logical system of dimension $d\ge1$ into $n\ge1$ finite subsystems of positive dimensions $d_i$. A located erasure replaces erased sites by fixed pure states and supplies an orthogonal location flag. Write $\epsilon_{\rm worst}=\sqrt{1-f_{\rm worst}^2}$, where one CPTP recovery is optimized before minimizing root entanglement fidelity over all unit vectors on $L\otimes R$, with $R\simeq L$. Write $\epsilon_e=\sqrt{1-f_e^2}$ for optimal root entanglement fidelity at the normalized maximally entangled input. Unless specified otherwise, single-site erasure is uniform. Assume the defining logical $SU(d)$ action, $d\ge2$, has a continuous transversal physical representation. Put $D=\max_i d_i$ and $e=\epsilon_{\rm worst}$. Both errors are positive and $$\ln D\ge\frac{\ln(d-1)-\ln(1+(2ne)^{-1})}{2ne},\qquad \ln D\ge(d-1)\ln\frac1{2end}.$$ In the second bound one can replace $e$ by $d\epsilon_e/2$. There are absolute $C>0$ and $d_0\ge2$, independent of the code and $n$, such that for $d\ge d_0$, $$e\ge\frac1{2n\ln D}-\frac{C}{nd},\qquad \frac d2\epsilon_e\ge\frac1{2n\ln D}-\frac{C}{nd}.$$ These quantify the local dimension cost of universal transversal gates.
-- source:
--   Continuous symmetries and approximate quantum error correction, arXiv:1902.07714v1, PDF p. 15, Theorem 4: Approximate Eastin-Knill theorem, Eqs.(51)–(52)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P22

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P22

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P22 (bell)

open QAlgorithms.Papers.Independent.Support21.P09 (Irreducible)

open QAlgorithms.Papers.Independent.Renew46.P45 (symmetricWeight)

/-- PDF pp.14–15, Theorem 4, (51),(52a),(52b), including the stated average variants.
The universal one-sided O constant is chosen before d,n and the code. -/
theorem approximate_eastin_knill :
    (∀ {d n : ℕ} (c : CovariantErasureCodeData d n), 2 ≤ d → SUCovariant c →
      0 < errorWorst c.uniformNoise ∧ 0 < errorE c.uniformNoise ∧
      c.logDim ≥ Real.log (d - 1 : ℝ) / (2 * n * errorWorst c.uniformNoise) -
        Real.log (1 + (2 * n * errorWorst c.uniformNoise)⁻¹) /
          (2 * n * errorWorst c.uniformNoise) ∧
      c.logDim ≥ (d - 1 : ℝ) * Real.log ((2 * errorWorst c.uniformNoise * n * d)⁻¹) ∧
      c.logDim ≥ (d - 1 : ℝ) * Real.log ((n * d ^ 2 * errorE c.uniformNoise)⁻¹)) ∧
    (∃ C : ℝ, 0 < C ∧ ∃ d0 : ℕ, 2 ≤ d0 ∧
      ∀ {d n : ℕ} (c : CovariantErasureCodeData d n), d0 ≤ d → SUCovariant c →
        errorWorst c.uniformNoise ≥ (2 * n * c.logDim)⁻¹ - C / (n * d) ∧
        (d : ℝ) * errorE c.uniformNoise / 2 ≥
          (2 * n * c.logDim)⁻¹ - C / (n * d)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P22

end
