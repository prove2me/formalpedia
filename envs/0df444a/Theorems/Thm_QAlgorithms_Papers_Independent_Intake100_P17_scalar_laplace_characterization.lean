-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P17_scalar_laplace_characterization
-- name    : QAlgorithms.Papers.Independent.Intake100.P17.scalar_laplace_characterization
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:27:33.592948+00:00
-- url     : https://prove2.me/theorems/215e38d5-8ccf-488c-acf3-b6fc981201f0
-- title:
--   Scalar reflection positivity is a finite Laplace mixture
-- statement:
--   Let \(\varphi:\mathbb R\to\mathbb C\) be continuous. Reflection positivity for \((\mathbb R,-\mathrm{id},(0,\infty))\) means that \(\varphi(x-y)\) is a positive definite kernel on \(\mathbb R\), \(\varphi\) is even, and \(\varphi(s+t)\) is positive definite for \(s,t>0\). This holds if and only if there is a finite positive Borel measure \(
--   u\) on \([0,\infty)\) for which
--   \[
--   \varphi(x)=\int_{[0,\infty)} e^{-\lambda|x|}\,d
--   u(\lambda)\qquad(x\in\mathbb R).
--   \]
--   The integrands are integrable. No condition \(\varphi(0)=1\) is imposed: \(
--   u\) can be zero and can have an atom at zero.
--
--   This characterizes all continuous scalar reflection-positive covariance functions on the real line.
-- source:
--   Reflection Positivity and Conformal Symmetry, arXiv:1206.2039v2, PDF p. 18, Corollary 3.3

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P17

noncomputable section

open scoped BigOperators Topology

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Intake100.P17

open QAlgorithms.Papers.Independent.Next46.P32 (PositiveKernel)

/-- Corollary 3.3, PDF p. 18: finite positive Borel measures, including zero and an
atom at zero. Explicit integrability prevents a total-integral default interpretation. -/
theorem scalar_laplace_characterization
    (phi : ℝ → ℂ) (hcont : Continuous phi) :
    ReflectionPositiveReal phi ↔
      ∃ nu : Measure {l : ℝ // 0 ≤ l}, IsFiniteMeasure nu ∧
        ∀ x : ℝ,
          Integrable (fun l => (Real.exp (-l.val * |x|) : ℂ)) nu ∧
          phi x = ∫ l, (Real.exp (-l.val * |x|) : ℂ) ∂nu := by sorry

end QAlgorithms.Papers.Independent.Intake100.P17

end
