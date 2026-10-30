-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P16_purification_entropy_identity
-- name    : QAlgorithms.Papers.Independent.Advance50.P16.purification_entropy_identity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:29:41.902025+00:00
-- url     : https://prove2.me/theorems/459bd7e9-80af-490b-be50-5cebafbdcb18
-- title:
--   Lemma 4: purification and complementary entropy identity
-- statement:
--   Let $\Phi:M_a\to M_a$ be CPT and suppose $\Phi(X)=\operatorname{Tr}_E[U(X\otimes|\tau\rangle\langle\tau|)U^\dagger]$, where $E$ is nonzero and finite, $U$ is unitary on $A\otimes E$, and $\|\tau\|=1$. For every density $\rho$ on $A$, there exist a nonzero finite reference $R$ and a unit vector $\psi\in R\otimes A$ with $\operatorname{Tr}_R|\psi\rangle\langle\psi|=\rho$. The explicitly constructed state $\gamma_{RAE}=(I_R\otimes U)(|\psi\rangle\langle\psi|\otimes|\tau\rangle\langle\tau|)(I_R\otimes U)^\dagger$, with the factors reassociated to $R,A,E$, is pure and satisfies
--
--   $$S(\gamma_{AE})-S(\gamma_E)=S(\gamma_R)-S(\gamma_{RA}).$$
--
--   All marginals are partial traces of this constructed state and entropy is in nats. The identity relates a channel dilation to complementary conditional entropies.
-- source:
--   Multiplicativity of completely bounded p-norms implies a new additivity result, arXiv:quant-ph/0506196v2, PDF p. 8, Lemma 4: purification and complementary entropy identity

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P16

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Topology

open Filter Set

namespace QAlgorithms.Papers.Independent.Advance50.P16

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact frozen counterparts; their bodies and conventions were checked for this repair.

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Dependency50.P19 (flip)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P30 (tensorMap)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P08 (depolarizing)

open QAlgorithms.Papers.Independent.Support50.P11 (wernerHolevoChannel)

/-- Lemma 4, PDF pp.8–9: the reference and purification are conclusions.
The channel's unitary representation and a normalized input/environment are the only data. -/
theorem purification_entropy_identity {A E : Type} [Fintype A] [Fintype E]
    [Nonempty A] [Nonempty E] (Phi : (Mat A →ₗ[ℂ] Mat A)) (hPhi : IsChannel Phi)
    (U : Matrix.unitaryGroup (A × E) ℂ) (tau : EuclideanSpace ℂ E) (htau : ‖tau‖ = 1)
    (hrep : ∀ X : Mat A, Phi X = traceRight
      (conjSuperop (U : Mat (A × E)) (Matrix.kronecker X (pureDensity tau))))
    (rho : Mat A) (hrho : IsDensityMatrix rho) :
    ∃ r : ℕ, 0 < r ∧ ∃ psi : EuclideanSpace ℂ (Fin r × A),
      ‖psi‖ = 1 ∧ traceLeft (pureDensity psi) = rho ∧
      let G := dilationState U tau psi
      (∃ eta : EuclideanSpace ℂ (Fin r × (A × E)), ‖eta‖ = 1 ∧ G = pureDensity eta) ∧
      entropy (traceLeft G) - entropy (traceLeft (traceLeft G)) =
        entropy (traceRight G) - entropy (traceRight (associateRAE G)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P16

end
