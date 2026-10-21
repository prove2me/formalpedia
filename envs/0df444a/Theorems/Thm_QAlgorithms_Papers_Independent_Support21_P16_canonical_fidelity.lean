-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P16_canonical_fidelity
-- name    : QAlgorithms.Papers.Independent.Support21.P16.canonical_fidelity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T04:40:08.471307+00:00
-- url     : https://prove2.me/theorems/51508871-e3b0-4411-b386-6268e04b297b
-- title:
--   State-independent global fidelity of the canonical cloner
-- statement:
--   Let $d>0$ and $1\le N<M$ be integers, $D_k=\binom{d+k-1}{k}$, and let $\widehat T_{MN}$ be the concrete map $(D_N/D_M)s_M((s_NAs_N)\otimes I^{\otimes(M-N)})s_M$, where $s_k$ is the Bose projector. For every unit vector $\phi\in\mathbb C^d$, put $\sigma=|\phi\rangle\langle\phi|$. Then
--   $$
--   \operatorname{Re}\operatorname{tr}\bigl(\sigma^{\otimes M}\widehat T_{MN}(\sigma^{\otimes N})\bigr)
--   =\frac{D_N}{D_M},
--   \qquad \mathcal F(\widehat T_{MN})=\frac{D_N}{D_M},
--   $$
--   where $\mathcal F$ is the infimum of this global overlap over all unit $\phi$.
--
--   This supplies both the exact overlap on each input and the worst-case value; it is distinct from the fidelity of a single output clone.
-- source:
--   Optimal Cloning of Pure States, arXiv:quant-ph/9804001v1, PDF p. 6, canonical-fidelity

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P16

noncomputable section

open scoped Matrix ComplexOrder

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Support21.P16

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

open QAlgorithms.Papers.Independent.Renew46.P45
  (TensorMat boseProjector powerVector IsCloningCovariant haarAverage)

attribute [local instance] QAlgorithms.Papers.Independent.Support21.P16.unitaryMeasurable

/-- PDF p.6 Eq.(3.5): every normalized pure input has the SAME global overlap;
its infimum is the dimension ratio. -/
theorem canonical_fidelity (d N M : ℕ) (hd : 0 < d) (hN : 1 ≤ N) (hNM : N < M) :
    (∀ phi : EuclideanSpace ℂ (Fin d), ‖phi‖ = 1 →
      cloningOverlap (canonicalCloner hNM.le) phi =
        (boseDimension d N : ℝ) / boseDimension d M) ∧
    cloningFidelity (canonicalCloner (d := d) hNM.le) =
      (boseDimension d N : ℝ) / boseDimension d M := by sorry

end QAlgorithms.Papers.Independent.Support21.P16

end
