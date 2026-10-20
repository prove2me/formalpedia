-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P19_goodType
-- name    : QAlgorithms.Papers.Independent.Dependency50.P19.goodType
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:23:10.188009+00:00
-- url     : https://prove2.me/theorems/5a974894-a254-4721-8284-8a24e2071bc4
-- title:
--   A realized good type with overlap, weight and purity control
-- statement:
--   All registers are finite dimensional and nonempty, pure sources have unit norm, logarithms and entropies are in bits, and $\|\cdot\|_1$ is the full Schatten trace norm.
--
--   Fix a normalized pure source and spectral decompositions of its marginals. There are a source-dependent constant $c>0$ and a nonnegative function $\iota(\delta)\to0$ as $\delta\downarrow0$ such that the following holds. For every local failure tolerance $\alpha\in(0,1/3)$ and frequency tolerance $\delta>0$, every sufficiently large $n$ has a realized typical type $t$ on $A$. Let $\psi'$ be the original block source, $\psi$ its normalized joint typical projection, and $\psi_t',\psi_t$ their normalized type projections. Put $P_t'=\operatorname{Tr}(\Pi_t\psi')$ and $P_t=\operatorname{Tr}(\Pi_t\psi)$. All projected vectors used here have positive norm, and
--
--   $$
--   |\langle\psi_t|\psi_t'\rangle|\ge1-18\alpha,\qquad
--   P_t\ge\tfrac13 P_t'\ge\tfrac13 2^{-n[c\delta+\iota(\delta)]},\qquad
--   \|\psi_t-\psi_t'\|_1\le12\sqrt\alpha.
--   $$
--
--   For $F=B,R$ the normalized density-matrix marginals also satisfy
--
--   $$\operatorname{Tr}[(\psi_t^F)^2]\le\frac{3}{1-3\alpha}\,2^{-n[H(F)-2c\delta-\iota(\delta)]}.$$
--
--   The restricted weights $P_t'$ form a subprobability family, and no exact flatness of $\psi_t^A$ is claimed. This supplies the usable good-type conclusion independently of the defective exact-flat bundle.
-- source:
--   The mother of all protocols: Restructuring quantum information's family tree, arXiv:quant-ph/0606225v1, PDF p. 23, Appendix A, Eqs. (A13)–(A14), pp.23–24

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P19

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P19

open MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P32 (purity)

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Appendix A, PDF pp.23–24, Eq.(A14): a good realized type with overlap,
positive nonnegligible weight, density-matrix distance and B,R purity bounds.
The restricted original type weights are a subprobability family; no normalization
of that family and no exact flatness of the jointly projected type state is assumed. -/
theorem goodType {R A B : Type*} [Fintype R] [Fintype A] [Fintype B]
    [DecidableEq R] [DecidableEq A] [DecidableEq B]
    [Nonempty R] [Nonempty A] [Nonempty B]
    (phi : EuclideanSpace ℂ (R × (A × B))) (hphi : IsState phi)
    (DA : Spectrum A) (DB : Spectrum B) (DR : Spectrum R)
    (hDA : DA.density = traceLeft (marginalRA (pureDensity phi)))
    (hDB : DB.density = traceLeft (marginalRB (pureDensity phi)))
    (hDR : DR.density = traceRight (pureDensity phi)) :
    ∃ c : ℝ, 0 < c ∧ ∃ iota : ℝ → ℝ,
      Filter.Tendsto iota (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
      (∀ delta > (0 : ℝ), 0 ≤ iota delta) ∧
      ∀ alpha > (0 : ℝ), alpha < 1/3 → ∀ delta > (0 : ℝ),
      ∃ N : ℕ, 0 < N ∧ ∀ n ≥ N,
        let PA := typicalProjector DA n delta
        let PB := typicalProjector DB n delta
        let PR := typicalProjector DR n delta
        let original := blockVector n phi
        let P := Matrix.kronecker PR (Matrix.kronecker PA PB)
        let projected := normalizeProjection P original
        0 < ‖act P original‖ ∧
        ∃ z : Fin n → A, Typical DA n delta z ∧
          let T : Matrix ((Fin n → R) × ((Fin n → A) × (Fin n → B)))
              ((Fin n → R) × ((Fin n → A) × (Fin n → B))) ℂ := onAlice (spectralTypeProjector DA z)
          let pt := (T * pureDensity projected).trace.re
          let ptOriginal := (T * pureDensity original).trace.re
          let v := normalizeProjection T projected
          let vOriginal := normalizeProjection T original
          0 < pt ∧ 0 < ptOriginal ∧ IsState v ∧ IsState vOriginal ∧
          1-18*alpha ≤ ‖inner ℂ v vOriginal‖ ∧
          ptOriginal/3 ≤ pt ∧
          Real.rpow 2 (-n*(c*delta+iota delta))/3 ≤ ptOriginal/3 ∧
          traceNorm (pureDensity v-pureDensity vOriginal) ≤ 12*Real.sqrt alpha ∧
          purity (traceLeft (marginalRB (pureDensity v))) ≤
            3/(1-3*alpha) * Real.rpow 2 (-n*(vnEntropy DB.density-2*c*delta-iota delta)) ∧
          purity (traceRight (pureDensity v)) ≤
            3/(1-3*alpha) * Real.rpow 2 (-n*(vnEntropy DR.density-2*c*delta-iota delta)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P19

end
