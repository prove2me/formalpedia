-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P07_decoupling_decoding
-- name    : QAlgorithms.Papers.Independent.Advance50.P07.decoupling_decoding
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:34:02.095478+00:00
-- url     : https://prove2.me/theorems/fce717ca-8056-4b9d-9240-6d832fb19503
-- title:
--   Decoupling fidelity implies decoding fidelity
-- statement:
--   Let $|\Omega\rangle^{RBE}$ be a unit vector on three nonzero finite-dimensional registers, and denote its computed reduced states by $\omega^{RB},\omega^{RE},\omega^R,\omega^E$. Fix any unit-vector purification $|\Psi\rangle^{RA}$ of $\omega^R$ in a nonzero finite-dimensional register $A$. There exists a CPTP decoder $D:\mathcal B(B)\to\mathcal B(A)$ such that
--
--   $$F(\omega^{RE},\omega^R\otimes\omega^E)^2\le F((\operatorname{id}_R\otimes D)(\omega^{RB}),\Psi^{RA})^2.$$
--
--   Here $\Psi^{RA}=|\Psi\rangle\langle\Psi|$ and $F(\rho,\sigma)=\operatorname{Tr}\sqrt{\sqrt\rho\sigma\sqrt\rho}$ is root fidelity. The decoder is chosen after the fixed purification; no equality of the dimensions of $R$ and $A$ is required. This converts environmental decoupling into achievable decoding accuracy.
-- source:
--   The quantum capacity of channels with arbitrarily correlated noise, arXiv:0902.0158v5, PDF p. 3, Lemma 4, decoupling fidelity implies decoding fidelity

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P07

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology

open Filter

namespace QAlgorithms.Papers.Independent.Advance50.P07

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Dependency50.P09 (relativeD petzD)

open QAlgorithms.Papers.Independent.Dependency50.P35 (maxRelative Density elog)

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Dependency50.P19 (marginalRA marginalRB)

open QAlgorithms.Papers.Independent.Support50.P21 (PositiveTensorBasis)

/-- Lemma 4, PDF p.3, (6). The purification is fixed before the decoder;
no equality of the A and R dimensions is required. -/
theorem decoupling_decoding {R B E A : Type} [Fintype R] [Fintype B] [Fintype E]
    [Fintype A] [DecidableEq R] [DecidableEq B] [DecidableEq E] [DecidableEq A]
    [Nonempty R] [Nonempty B] [Nonempty E] [Nonempty A]
    (Omega : EuclideanSpace ℂ (R × (B × E))) (hOmega : ‖Omega‖ = 1)
    (Psi : EuclideanSpace ℂ (R × A)) (hPsi : ‖Psi‖ = 1)
    (hpur : traceRight (pureDensity Psi) = traceRight (marginalRA (pureDensity Omega))) :
    ∃ D : Superop B A, IsChannel D ∧
      rootFidelity (marginalRB (pureDensity Omega))
        (Matrix.kronecker (traceRight (marginalRA (pureDensity Omega)))
          (traceLeft (marginalRB (pureDensity Omega)))) ^ 2 ≤
      rootFidelity (idTensorSuperop D (marginalRA (pureDensity Omega))) (pureDensity Psi) ^ 2 := by sorry

end QAlgorithms.Papers.Independent.Advance50.P07

end
