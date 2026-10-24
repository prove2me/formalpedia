-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P15_remark5
-- name    : QAlgorithms.Papers.Independent.Support50.P15.remark5
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:38:38.886289+00:00
-- url     : https://prove2.me/theorems/65554862-6d8a-4f9f-8a47-2f078e606a3b
-- title:
--   remark5
-- statement:
--   For each finite $d\ge2$, the sharp entropy-difference bound $M(\Delta,d)$ is strictly decreasing on $[-\log d,0]$ and strictly increasing on $[0,\log d]$. More precisely, for $0<\lambda<1$ and nonzero $\Delta\in[-\log d,\log d]$,
--
--   $$M(\lambda\Delta,d)<\lambda M(\Delta,d).$$
--
--   The comparison is in the extended real order and includes $M(\log d,d)=+\infty$. This describes both monotonicity branches and a strict scaling inequality.
-- source:
--   Tight bound on relative entropy by entropy difference, arXiv:1304.0036v3, PDF p. 5, remark5

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P15

noncomputable section

attribute [local instance] Classical.propDecidable

open scoped Matrix ComplexConjugate ENNReal Matrix.Norms.L2Operator

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Support50.P15

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

/-- Remark 5, PDF pp.5--6, including strict scaling at the infinite endpoint. -/
theorem remark5 (d : ℕ) (hd : 2 ≤ d) :
    StrictAntiOn (tightBound d) (Set.Icc (-Real.log d) 0) ∧
    StrictMonoOn (tightBound d) (Set.Icc 0 (Real.log d)) ∧
    (∀ delta ∈ Set.Icc (-Real.log d) (Real.log d), delta ≠ 0 →
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, tightBound d (t * delta) < (t : EReal) * tightBound d delta) := by sorry

end QAlgorithms.Papers.Independent.Support50.P15

end
