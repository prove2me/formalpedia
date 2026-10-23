-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P19_degradingRangeContainment
-- name    : QAlgorithms.Papers.Independent.Gap20.P19.degradingRangeContainment
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T07:33:31.136969+00:00
-- url     : https://prove2.me/theorems/010ba47f-f705-4cb0-bb32-c42624455718
-- title:
--   Lemma 9
-- statement:
--   All Hilbert spaces are finite dimensional, complex, and nonzero. A channel is completely positive and trace preserving on every operator. Write $r(\Phi)$ for its Choi rank, the minimum pure-environment dimension. Receiver and complementary channels are always obtained from the same isometry.
--
--   Let $U$ be an isometric dilation of $\Phi$, and let $D$ be a CPTP map satisfying $D\circ\Phi=\Phi^C$ on every operator. For a unit input vector $\psi$, put $B_\psi=\operatorname{range}\Phi(|\psi\rangle\langle\psi|)$ and $E_\psi=\operatorname{range}\Phi^C(|\psi\rangle\langle\psi|)$. Every vector $\phi\in B_\psi$, including unnormalized vectors, satisfies
--   $$\operatorname{range}D(|\phi\rangle\langle\phi|)\subseteq E_\psi.$$
--
--   This controls the action of a particular degrader on pure-output support subspaces.
-- source:
--   The structure of degradable quantum channels, arXiv:0802.1360v2, PDF p. 16, Lemma 9

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P19

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P19

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Kronecker

open Filter Topology

open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel IsDegradable IsAntidegradable
   maximumCoherentInformation dilationPower)

open QAlgorithms.Papers.Independent.Claimed50.P48
  (MinimalDilation indexedKrausDilation arbitraryVectorComplement superopTensor tensorDilation)

open QAlgorithms.Papers.Independent.Claimed50.P24 (ChannelEB)

open QAlgorithms.Papers.Independent.Information100.P60 (wernerHolevo)

open QAlgorithms.Papers.Independent.Gap48.P36 (finWeyl WeylLabel)

open QAlgorithms.Papers.Independent.Information100.P69 (choi)

open QAlgorithms.Papers.Independent.Information100.P50 (matrixRange)

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C E F R K A2 B2 E2 : Type}

variable [Fintype A] [DecidableEq A] [Nonempty A]

variable [Fintype B] [DecidableEq B] [Nonempty B]

variable [Fintype C] [DecidableEq C] [Nonempty C]

variable [Fintype E] [DecidableEq E] [Nonempty E]

variable [Fintype F] [DecidableEq F] [Nonempty F]

variable [Fintype R] [DecidableEq R] [Nonempty R]

variable [Fintype K] [DecidableEq K]

variable [Fintype A2] [DecidableEq A2] [Nonempty A2]

variable [Fintype B2] [DecidableEq B2] [Nonempty B2]

variable [Fintype E2] [DecidableEq E2] [Nonempty E2]

/-- Lemma 9, PDF pp.16–17. The contained vector need not be normalized;
its zero case gives the zero range. The degrader is CPTP on all operators. -/
theorem degradingRangeContainment [Nonempty A] [Nonempty B] [Nonempty E]
    (U : Matrix (B × E) A ℂ) (hU : IsIsometry U)
    (D : Superop B E) (hD : IsChannel D)
    (hdegrade : ∀ rho, D (receiverChannel U rho) = complementaryChannel U rho)
    (psi : EuclideanSpace ℂ A) (hpsi : IsState psi)
    (phi : EuclideanSpace ℂ B)
    (hphi : (fun b => phi b) ∈ matrixRange (receiverChannel U (pureDensity psi))) :
    matrixRange (D (pureDensity phi)) ≤ matrixRange (complementaryChannel U (pureDensity psi)) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P19

end
