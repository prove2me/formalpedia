-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P44_charge_resolved_necessary
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P44.charge_resolved_necessary
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:22:43.659644+00:00
-- url     : https://prove2.me/theorems/5f9d24f1-f83a-4a38-885a-0d525cf7d629
-- title:
--   Necessary charge-resolved correction condition
-- statement:
--   All Hilbert spaces are finite dimensional and nonzero, and every channel is completely positive and trace preserving on the full matrix algebra. Let $P_1,\ldots,P_r$ be nonzero orthogonal Hermitian sector projectors summing to $I$, let $C=\sum_i c_iP_i$ have pairwise distinct real eigenvalues, and put $\mathcal P(X)=\sum_iP_iXP_i$. Let $\mathcal N(X)=\sum_nE_nXE_n^\dagger$ have a finite normalized Kraus family and satisfy $\mathcal P\mathcal N\mathcal P=\mathcal P\mathcal N$. Let $W$ be an isometry from a nonzero logical space. Correctability means existence of a CPTP $\mathcal R$ with $\mathcal P\mathcal R\mathcal P=\mathcal P\mathcal R$ and $\mathcal R\mathcal N(WXW^\dagger)=\mathcal P(WXW^\dagger)$ for every logical matrix $X$. If the code is correctable, then one complex array $(c_{ijnm})$ satisfies
--
--   $$
--   W^\dagger E_n^\dagger P_jE_mW=\sum_i c_{ijnm}W^\dagger P_iW\quad\text{for all }j,n,m.
--   $$
--
--   This necessary linear condition alone is not asserted sufficient for an arbitrary code.
-- source:
--   Approximate recovery with locality and symmetry constraints, arXiv:1806.10324v2, PDF p. 5, Corollary 6, Eq.(21): necessary charge-resolved correction condition

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

/-- PDF p.5, Corollary 6, Eq.(21): necessity only, without code invariance. -/
theorem charge_resolved_necessary [Nonempty H] [Nonempty L] {r : ℕ}
    (s : Sectors H r) (A : J → Mat H) (hA : IsKrausFamily A)
    (hphys : IsPhysicalChannel (sectorProject s) (sectorProject s) (krausApply A))
    (W : Matrix H L ℂ) (hW : Wᴴ * W = 1)
    (hcorr : PhysicallyCorrectable (sectorProject s) (krausApply A) W) :
    ChargeCoefficients s A W := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P44

end
