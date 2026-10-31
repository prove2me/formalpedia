-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P01_haar_partial_isometry_moments
-- name    : QAlgorithms.Papers.Independent.Intake100.P01.haar_partial_isometry_moments
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:52:18.491452+00:00
-- url     : https://prove2.me/theorems/978c024a-84aa-495c-940b-4e998e7c1ae7
-- title:
--   Lemma 6: Haar partial-isometry first and second moments
-- statement:
--   Let $|\psi\rangle_{ABR}$ be a unit vector, $d=\dim A>0$, $1\le L\le d$, and $D>0$ with $\operatorname{Tr}\rho_B^2\le1/D$. Fix a coisometry $P_0:A\to\mathbb C^L$ with $P_0P_0^\dagger=I$, draw $U$ from normalized Haar measure on $U(d)$, and set $P=P_0U$ and $\omega=(P\otimes I_R)\rho_{AR}(P\otimes I_R)^\dagger$. With $\mu=(L/d)\tau_L\otimes\rho_R$,
--   $$\mathbb E\omega=\mu,\qquad \mathbb E\|\omega-\mu\|_2^2\le\frac{L^2}{d^2D},\qquad \mathbb E\|\omega-\mu\|_1\le\frac Ld\sqrt{\frac{L\dim R}{D}}.$$
--   The norms are respectively Hilbert–Schmidt and unhalved trace norm. The displayed matrix and scalar integrands are integrable. These are the moment estimates for random partial-isometry decoupling, including $d=L=1$.
-- source:
--   Quantum state merging and negative information, arXiv:quant-ph/0512247v1, PDF p. 7, Lemma 6: Haar partial-isometry first and second moments

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P01

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P01

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

open MeasureTheory

open QAlgorithms.Papers.Independent.Gap20.P11 (IsLOCC productApply finTransport referenceInformation)

open QAlgorithms.Papers.Independent.Bridge50.P40
  (RankMergingCode OneWayMergingCode mergingFidelity SourceProtocolAchievable)

open QAlgorithms.Papers.Independent.Dependency50.P19
  (first marginalRA marginalRB motherTarget motherOutput sourceCopies swap mutualInformation)

open QAlgorithms.Papers.Independent.Information100.P67 (conditionalEntropy)

open QAlgorithms.Papers.Independent.Information100.P32 (purity)

open QAlgorithms.Papers.Independent.Advance50.P29 (weakTypicalProjector)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.7, Lemma 6: first moment, expected SQUARED Hilbert--Schmidt
norm, and expected trace norm. The first matrix moment and its integrability
are stated entrywise over complex scalars, equivalently in finite dimension.
The purity bound on Bob is inherited from Proposition 4.
The d=L=1 case is included and has zero variance. -/
theorem haar_partial_isometry_moments {B R : Type} [Fintype B] [Fintype R]
    [Nonempty B] [Nonempty R] (d L : ℕ) (hd : 0 < d) (hL : 0 < L) (hLd : L ≤ d)
    (P0 : Matrix (Fin L) (Fin d) ℂ) (hP0 : P0 * P0ᴴ = 1)
    (psi : EuclideanSpace ℂ (R × (Fin d × B))) (hpsi : IsState psi)
    (D : ℝ) (hD : 0 < D)
    (hpurity : purity (traceLeft (traceLeft (pureDensity psi))) ≤ 1 / D) :
    let omega := randomOmega P0 (marginalRA (pureDensity psi))
    let mean := (((L : ℝ) / d : ℝ) : ℂ) • decoupled L (traceRight (pureDensity psi))
    (∀ i j : R × Fin L,
      Integrable (fun U => omega U i j) (Schur.unitaryHaar d) ∧
      (∫ U, omega U i j ∂(Schur.unitaryHaar d)) = mean i j) ∧
    Integrable (fun U => frobNorm (omega U - mean) ^ 2) (Schur.unitaryHaar d) ∧
    (∫ U, frobNorm (omega U - mean) ^ 2 ∂(Schur.unitaryHaar d)) ≤
      (L : ℝ)^2 / (d : ℝ)^2 / D ∧
    Integrable (fun U => traceNorm (omega U - mean)) (Schur.unitaryHaar d) ∧
    (∫ U, traceNorm (omega U - mean) ∂(Schur.unitaryHaar d)) ≤
      (L : ℝ) / d * Real.sqrt ((L : ℝ) * Fintype.card R / D) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P01

end
