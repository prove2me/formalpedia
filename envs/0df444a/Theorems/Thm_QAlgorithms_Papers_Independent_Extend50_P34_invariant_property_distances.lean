-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P34_invariant_property_distances
-- name    : QAlgorithms.Papers.Independent.Extend50.P34.invariant_property_distances
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:45:34.31298+00:00
-- url     : https://prove2.me/theorems/1ccc9b0b-c117-4c2d-b9e5-0a778687622f
-- title:
--   Proposition 2.2
-- statement:
--   Let $P$ be a closed unitarily invariant set of $d$-dimensional density matrices and let $\rho$ be a density matrix. Trace distance and decreasing-spectrum total variation give identical distances to $P$:
--
--   $$d_{\rm tr}(\rho,P)=d_{\rm TV}^{\rm sym}(\rho,P).$$
--
--   Equivalently, every real separation threshold from all members is the same for both distances. If $P$ is nonempty, the common minimum is attained. The separation formulation also covers $P=\varnothing$ and shows that the two testing models have identical promises.
-- source:
--   Quantum Spectrum Testing, arXiv:1501.05028v1, PDF p. 11, Proposition 2.2

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P34

noncomputable section

open scoped Matrix BigOperators

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P34

attribute [local instance] Classical.propDecidable

-- Reuse exact pinned definitions; these are imports, not local declarations.

open QAlgorithms.Papers.Independent.Support50.P38 (tv wordMass)

open QAlgorithms.Papers.Independent.Advance50.P28 (counts)

/-- Proposition 2.2, arXiv:1501.05028v1, PDF p.11. Use all-member separation for empty P, avoiding real infimum defaults. Nonempty closed P is compact inside the density matrices. -/
theorem invariant_property_distances
    (d : ℕ) (hd : 0 < d) (P : Set (Matrix (Fin d) (Fin d) ℂ))
    (hclosed : IsClosed P) (hstate : ∀ rho ∈ P, IsDensityMatrix rho)
    (hinv : ∀ rho (U : Matrix.unitaryGroup (Fin d) ℂ),
      ((U : Matrix _ _ ℂ) * rho * star (U : Matrix _ _ ℂ)) ∈ P ↔ rho ∈ P)
    (rho : Matrix (Fin d) (Fin d) ℂ) (hrho : IsDensityMatrix rho) :
    (∀ epsilon : ℝ,
      (∀ sigma ∈ P, epsilon ≤ traceDistance rho sigma) ↔
      (∀ sigma ∈ P, epsilon ≤ tv (decreasingSpectrum rho) (decreasingSpectrum sigma))) ∧
    (P.Nonempty → ∃ sigma ∈ P,
      (∀ tau ∈ P, traceDistance rho sigma ≤ traceDistance rho tau) ∧
      ∀ tau ∈ P, traceDistance rho sigma ≤ tv (decreasingSpectrum rho) (decreasingSpectrum tau)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P34

end
