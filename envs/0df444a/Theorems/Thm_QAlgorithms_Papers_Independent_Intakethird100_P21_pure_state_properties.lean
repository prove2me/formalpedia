-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P21_pure_state_properties
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P21.pure_state_properties
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:52:54.648347+00:00
-- url     : https://prove2.me/theorems/7303e890-d4d2-4629-a82a-5712797627f0
-- title:
--   Pure tangle: Schmidt formula, local invariance and range
-- statement:
--   Let $d_A,d_B>0$, $r=\min(d_A,d_B)$, and let $\psi$ be a normalized bipartite pure state. Schmidt probabilities $\mu_j\ge0$ satisfy $\sum_j\mu_j=1$ and enter its Schmidt expansion as amplitudes $\sqrt{\mu_j}$ in orthonormal local families. With $C$ the I-concurrence roof, $\tau$ the pure-tangle roof, and $T(\psi)=2(1-\operatorname{tr}\rho_A^2)$ for $\rho_A=\operatorname{Tr}_B|\psi\rangle\langle\psi|$,
--
--   $$
--   \tau(|\psi\rangle\langle\psi|)=C(\psi)^2=T(\psi)=2\Bigl(1-\sum_j\mu_j^2\Bigr)=4\sum_{j<k}\mu_j\mu_k,
--   \qquad 0\le T(\psi)\le\frac{2(r-1)}r.
--   $$
--
--   The concurrence roof also agrees with pure concurrence on the pure projector. The pure tangle is smooth on normalized vectors and invariant under arbitrary local unitaries. It is zero exactly on normalized product states, and reaches its upper endpoint exactly on states with all $r$ Schmidt probabilities equal to $1/r$. For $r=1$ the two endpoints coincide at zero.
--
--   This identifies the pure cost underlying the two distinct convex roofs.
-- source:
--   I-concurrence and tangle for isotropic states, arXiv:quant-ph/0208002v1, PDF p. 4, §2, (2.2): Schmidt expression, local-unitary invariance and range of pure tangle

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P21

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P21

open scoped Matrix ComplexConjugate

open Filter

open QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P03
  (PureEnsemble convexRoof pureConcurrence concurrence SchmidtData schmidtVector)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.4, (2.2): Schmidt formula, smoothness, local-unitary invariance,
pure-roof agreement, range, and its product/maximally-entangled endpoints.
The min(dA,dB)=1 case is retained. -/
theorem pure_state_properties (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ContDiffOn ℝ ⊤ (pureTangle (I := Fin a) (J := Fin b)) {psi | IsState psi} ∧
    (∀ s : SchmidtData a b,
      IsState (schmidtVector s) ∧
      pureTangle (schmidtVector s) = schmidtCost s.probability ∧
      schmidtCost s.probability =
        4 * ∑ i, ∑ j, (if i < j then s.probability i * s.probability j else 0)) ∧
    (∀ psi : EuclideanSpace ℂ (Fin a × Fin b), IsState psi →
      tangle (pureDensity psi) = pureTangle psi ∧
      concurrence (pureDensity psi) = pureConcurrence psi ∧
      pureConcurrence psi ^ 2 = pureTangle psi ∧
      0 ≤ pureTangle psi ∧ pureTangle psi ≤ 2 * ((min a b : ℝ) - 1) / min a b ∧
      (pureTangle psi = 0 ↔ IsPureProductState psi) ∧
      (pureTangle psi = 2 * ((min a b : ℝ) - 1) / min a b ↔ IsMaximallyEntangled psi) ∧
      ∀ U : Matrix.unitaryGroup (Fin a) ℂ, ∀ V : Matrix.unitaryGroup (Fin b) ℂ,
        pureTangle (act (Matrix.kronecker (U : Matrix (Fin a) (Fin a) ℂ)
          (V : Matrix (Fin b) (Fin b) ℂ)) psi) = pureTangle psi) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P21

end
