-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P19_jointTypical
-- name    : QAlgorithms.Papers.Independent.Dependency50.P19.jointTypical
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:22:16.653339+00:00
-- url     : https://prove2.me/theorems/54fe5ee9-1f37-4a55-acc1-ccaa302e5461
-- title:
--   Simultaneous typical projection properties
-- statement:
--   All registers are finite dimensional and nonempty, pure sources have unit norm, logarithms and entropies are in bits, and $\|\cdot\|_1$ is the full Schatten trace norm.
--
--   Fix $\phi^{RAB}$ and spectral decompositions of its three marginals, including possible zero eigenvalues. Typical sequences are restricted to positive spectral support. For every $\epsilon,\delta>0$, there is a positive frequency tolerance $\tau\le\delta$ and an integer threshold such that every subsequent block length admits its three spectral typical projectors $\Pi_F$, $F\in\{R,A,B\}$. Let $\psi$ be the normalized joint projection of $\phi^{\otimes n}$. The projection has positive probability, $\psi$ is normalized, and
--
--   $$
--   \|\psi-\phi^{\otimes n}\|_1\le\epsilon,\qquad
--   2^{n(H(F)-\delta)}\le\operatorname{rank}\Pi_F\le2^{n(H(F)+\delta)},\qquad
--   \operatorname{Tr}[(\psi^F)^2]\le2^{-n(H(F)-\delta)}.
--   $$
--
--   Moreover, there is a normalized fallback vector in Alice's typical range for which the Schumacher project-and-replace map is CPTP and its action on Alice, tensored with identity on the other registers, disturbs the original joint source by at most $\epsilon$ in full trace norm.
--
--   These simultaneous properties supply the operational typical truncation used by the memoryless mother theorem.
-- source:
--   The mother of all protocols: Restructuring quantum information's family tree, arXiv:quant-ph/0606225v1, PDF p. 12, Section VII; Appendix A, pp.22–23

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P19

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P19

open MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P32 (purity)

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Appendix A and Section VII, PDF pp.12,22–23: simultaneous typical
projection, compression disturbance, rank windows and normalized marginal purities.
Frequency tolerance is chosen smaller than the requested entropy slack. -/
theorem jointTypical {R A B : Type*} [Fintype R] [Fintype A] [Fintype B]
    [DecidableEq R] [DecidableEq A] [DecidableEq B]
    [Nonempty R] [Nonempty A] [Nonempty B]
    (phi : EuclideanSpace ℂ (R × (A × B))) (hphi : IsState phi)
    (DA : Spectrum A) (DB : Spectrum B) (DR : Spectrum R)
    (hDA : DA.density = traceLeft (marginalRA (pureDensity phi)))
    (hDB : DB.density = traceLeft (marginalRB (pureDensity phi)))
    (hDR : DR.density = traceRight (pureDensity phi)) :
    ∀ eps > (0 : ℝ), ∀ delta > (0 : ℝ),
    ∃ tau : ℝ, 0 < tau ∧ tau ≤ delta ∧ ∃ N : ℕ, 0 < N ∧ ∀ n ≥ N,
      let PA := typicalProjector DA n tau
      let PB := typicalProjector DB n tau
      let PR := typicalProjector DR n tau
      let original := blockVector n phi
      let P := Matrix.kronecker PR (Matrix.kronecker PA PB)
      let projected := normalizeProjection P original
      0 < ‖act P original‖ ∧ IsState projected ∧
      traceNorm (pureDensity projected - pureDensity original) ≤ eps ∧
      RankWindow n (vnEntropy DA.density) delta PA ∧
      RankWindow n (vnEntropy DB.density) delta PB ∧
      RankWindow n (vnEntropy DR.density) delta PR ∧
      purity (traceLeft (marginalRA (pureDensity projected))) ≤
        Real.rpow 2 (-n*(vnEntropy DA.density-delta)) ∧
      purity (traceLeft (marginalRB (pureDensity projected))) ≤
        Real.rpow 2 (-n*(vnEntropy DB.density-delta)) ∧
      purity (traceRight (pureDensity projected)) ≤
        Real.rpow 2 (-n*(vnEntropy DR.density-delta)) ∧
      ∃ fallback : EuclideanSpace ℂ (Fin n → A), IsState fallback ∧ act PA fallback = fallback ∧
        IsChannel (schumacher PA fallback) ∧
        traceNorm (idTensorSuperop (first (schumacher PA fallback)) (pureDensity original) -
          pureDensity original) ≤ eps := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P19

end
