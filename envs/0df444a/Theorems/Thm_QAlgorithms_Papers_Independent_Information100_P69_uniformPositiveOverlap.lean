-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P69_uniformPositiveOverlap
-- name    : QAlgorithms.Papers.Independent.Information100.P69.uniformPositiveOverlap
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:08:00.724585+00:00
-- url     : https://prove2.me/theorems/65784b75-fd6e-4ad7-a5ba-19b64b9a2ac1
-- title:
--   A branch with uniform positive overlap
-- statement:
--   Let $J:H\to K$ be an isometry and $M$ a CPTP map. Fix $0<\delta<1$ and compute $\beta=b_\delta(\operatorname{Ad}_J,M)>0$, the single-alternative testing optimum. Set $r=\sqrt{1-\delta}$ and $c=(1-r)/(1+r)$. There exists one operator $V:H\to K$ such that
--   $$\|V\|_\infty\le1,\qquad\operatorname{Re}(J^\dagger V)\ge cI,\qquad M\ge_{\rm CP}\beta\operatorname{Ad}_V.$$
--   This extracts a uniformly positive-overlap branch. The coefficient $\beta$ is not asserted to be an input-independent branch probability.
--
--   The testing model uses one normalized pure input, possibly entangled across uses and with a reference, and one acceptance effect shared by every alternative. The symbol $\le_{\rm CP}$ means that the difference of the larger and smaller maps is completely positive; $\|\cdot\|_\diamond$ is the full diamond norm. Information quantities use base-2 logarithms.
-- source:
--   A Generalized Stein Lemma for Quantum Channels, arXiv:2609.30762v1, PDF p. 25, Lemma 25

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P69

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Information100.P69

attribute [local instance] Classical.propDecidable Classical.decEq

section Statements

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- Lemma 25, positive-overlap branch at the computed testing coefficient, PDF pp.25–28. -/
theorem uniformPositiveOverlap [Nonempty A] [Nonempty B] (J : Matrix B A ℂ) (hJ : J.conjTranspose*J = 1)
    (M : Superop A B) (hM : IsChannel M) (delta : ℝ) (hdelta : 0 < delta) (hdelta1 : delta < 1)
    (hbeta : 0 < simpleBeta (conjSuperop J) M delta) :
    let r := Real.sqrt (1-delta)
    let c := (1-r)/(1+r)
    ∃ V : Matrix B A ℂ, specNorm V ≤ 1 ∧
      (hermitianPart (J.conjTranspose*V)-(c:ℂ) • 1).PosSemidef ∧
      CPLe ((simpleBeta (conjSuperop J) M delta:ℂ) • conjSuperop V) M := by sorry

end Statements

end QAlgorithms.Papers.Independent.Information100.P69

end
