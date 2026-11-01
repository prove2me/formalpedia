-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P44_majorana_ring_geometric_correction
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P44.majorana_ring_geometric_correction
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:29:29.992313+00:00
-- url     : https://prove2.me/theorems/7952993f-f70e-4e57-ac95-7db805989085
-- title:
--   Geometric support ensures exact Majorana-ring correction
-- statement:
--   All Hilbert spaces are finite dimensional and nonzero, and every channel is completely positive and trace preserving on the full matrix algebra. Consider $2n$ Majorana operators $w_a=w_a^\dagger$ on the $2^n$-dimensional Fock space, satisfying $\{w_a,w_b\}=2\delta_{ab}I$. There are $2k>0$ free modes in cyclic order, with even-length intervals $I_j$ of nearest-neighbor paired modes between consecutive free modes. The isometry $W$ encodes all $2^k$ free-mode states and initializes each paired fermion in its specified vacuum; its range projector is the product of the paired-mode vacuum projectors. Write $C$ for total parity and $\mathcal P(X)=(X+CXC)/2$. Let $d=\min_j|I_j|$. Let $\mathcal N(X)=\sum_iE_iXE_i^\dagger$ have a normalized finite Kraus family. Suppose each whole $E_i$ is an even Majorana polynomial supported on some cyclic interval of length $\ell_i$ with $2\ell_i\le d$. The intervals may differ with $i$. Then, writing $P_\pm=(I\pm C)/2$, there is one complex array $\lambda_{ijs}$ such that
--
--   $$
--   W^\dagger E_i^\dagger E_j(P_sBP_s)W=\lambda_{ijs}W^\dagger(P_sBP_s)W
--   $$
--
--   for every $i,j,s$ and every $B$ commuting with the whole-chain even algebra. Moreover a CPTP recovery strongly local to that algebra exactly recovers $\mathcal P$ on the code. If $d=0$, only scalar Kraus operators meet the support condition.
--
--   This is finite exact correction under geometric support, without a common support region for the channel or a standard full-code Knill–Laflamme assertion.
-- source:
--   Approximate recovery with locality and symmetry constraints, arXiv:1806.10324v2, PDF p. 10, §IV F: geometric support implies exact correction on the Majorana ring

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P44

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P44

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Information100.P67 (mapFirst)

open QAlgorithms.Papers.Independent.Claimed50.P48 (operatorTraceDual)

open QAlgorithms.Papers.Independent.Renew46.P43 (purification)

variable {H K L J E F B : Type*}

variable [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]

variable [Fintype L] [DecidableEq L] [Fintype J] [DecidableEq J]

variable [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F]

variable [Fintype B] [DecidableEq B]

/-- PDF pp.10--11, Section IV F: each even Kraus operator may have its OWN
geometric interval, of length at most half the shortest paired interval.
Conclusion is Eq.(54) and exact strong-local physical correction; the disputed
whole-code standard-KL reduction is not used or asserted. 
Parity correction, PDF p.2 Eq.(1): printed i^(|omega|-1) for Majorana labels;
changed to i^m on 2m ordered modes. Why: the printed four-mode value is
anti-Hermitian with square -I, whereas the source requires parity sectors of
a Hermitian involution. Only this normalization (up to sign) is corrected. -/
theorem majorana_ring_geometric_correction {n k : ℕ}
    (f : Fermions n) (r : RingLayout n k) (code : RingCode f r)
    (noise : J → Mat (Fin (2 ^ n))) (hnoise : IsKrausFamily noise)
    (hsupport : ∀ j, ∃ length : ℕ, 2 * length ≤ minimumGap r ∧
      HasIntervalSupport f (noise j) length) :
    RegionalCoefficients (evenRegion f Finset.univ : Set _) (totalParity f)
      noise code.W ∧
    StrongCorrectable (evenRegion f Finset.univ : Set _) (totalParity f)
      (krausApply noise) code.W := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P44

end
