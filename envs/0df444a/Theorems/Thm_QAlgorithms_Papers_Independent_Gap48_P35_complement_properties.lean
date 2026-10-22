-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P35_complement_properties
-- name    : QAlgorithms.Papers.Independent.Gap48.P35.complement_properties
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:50:32.482079+00:00
-- url     : https://prove2.me/theorems/fb0a0e89-2d74-4dc8-a262-06c9fd2ec5fb
-- title:
--   §II unnumbered: reciprocity and fixed-space uniqueness of B-complements
-- statement:
--   All systems are finite nonzero-dimensional complex quantum systems. Density states are positive semidefinite with trace one, and $S$ is von Neumann entropy in bits. Write $E_f$ for formation, $I^{\leftarrow}$ for maximal Holevo correlation measured on the second party, $E_C$ for asymptotic singlet preparation cost, $E_D$ for EPR distillation rate, $C_D$ for net common randomness, and $K$ for secret-key rate. A left arrow means communication from the second legitimate party to the first. Key secrecy includes all public transcripts. Asymptotic tasks use independent copies, vanishing error and no extra initially shared resource.
--
--   Write $\rho_{AB}\sim\sigma_{AC}$ when a common normalized pure state has these marginals. Complementarity implies equality of the $A$ marginals. If $\sigma_{AC}$ and $\tau_{AC}$ both complement $\rho_{AB}$ on the same ambient $A\otimes C$ space, a unitary $U_C$ relates them as displayed.
--
--   $$
--   \rho_{AB}\sim\sigma_{AC}\iff\sigma_{AC}\sim\rho_{AB},\qquad \sigma_{AC}=(1_A\otimes U_C)\tau_{AC}(1_A\otimes U_C)^\dagger.
--   $$
--
--   This records reciprocity and local-unitary uniqueness, fixing the complement space.
-- source:
--   Monogamy of entanglement and other correlations, arXiv:quant-ph/0310037v1, PDF p. 2, §II unnumbered: reciprocity and fixed-space uniqueness of B-complements

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P35

namespace QAlgorithms.Papers.Independent.Gap48.P35

open scoped Matrix ComplexConjugate ComplexOrder

open Filter Topology

open Information100.P21 (Op)

open Information100.P08 (IsPure formation measuredCorrelation)

open Dependency50.P19 (marginalRA marginalRB)

noncomputable section

/-- PDF p.2, §II: reciprocity, common A marginal, and uniqueness under a unitary on the SAME ambient C (the source Bprime). -/
theorem complement_properties {A : Type} {B : Type} {C : Type}
    [Fintype A] [DecidableEq A] [Nonempty A] [Fintype B] [DecidableEq B] [Nonempty B] [Fintype C] [DecidableEq C] [Nonempty C]
    (rho : Op (A × B)) (sigma : Op (A × C))
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) :
    (BComplement rho sigma ↔ BComplement sigma rho) ∧
      (BComplement rho sigma →
        traceRight rho = traceRight sigma ∧
        ∀ sigma2 : Op (A × C), BComplement rho sigma2 →
          ∃ U : Matrix.unitaryGroup C ℂ,
            sigma = Matrix.kronecker (1 : Op A) (U : Op C) * sigma2 *
              (Matrix.kronecker (1 : Op A) (U : Op C))ᴴ) := by sorry

end

end QAlgorithms.Papers.Independent.Gap48.P35
