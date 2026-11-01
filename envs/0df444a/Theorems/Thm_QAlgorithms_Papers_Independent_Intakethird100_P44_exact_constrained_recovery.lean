-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P44_exact_constrained_recovery
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P44.exact_constrained_recovery
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:21:54.022194+00:00
-- url     : https://prove2.me/theorems/7b256b20-7764-4811-870f-9cac57088c4b
-- title:
--   Exact constrained recovery with positive conditional states
-- statement:
--   All Hilbert spaces are finite dimensional and nonzero, and every channel is completely positive and trace preserving on the full matrix algebra. Let $P_1,\ldots,P_r$ be nonzero orthogonal Hermitian sector projectors summing to $I$, let $C=\sum_i c_iP_i$ have pairwise distinct real eigenvalues, and put $\mathcal P(X)=\sum_iP_iXP_i$. Let $\mathcal N(X)=\sum_nE_nXE_n^\dagger$ have a finite normalized Kraus family and satisfy $\mathcal P\mathcal N\mathcal P=\mathcal P\mathcal N$. Let $W$ be an isometry from a nonzero logical space. Correctability means existence of a CPTP $\mathcal R$ with $\mathcal P\mathcal R\mathcal P=\mathcal P\mathcal R$ and $\mathcal R\mathcal N(WXW^\dagger)=\mathcal P(WXW^\dagger)$ for every logical matrix $X$. The code is correctable if and only if there exist environment matrices $\sigma_{j|i}$ such that
--
--   $$
--   \sigma_{j|i}\succeq0,\qquad\sum_j\operatorname{Tr}\sigma_{j|i}=1\quad\text{for each }i,
--   $$
--   $$
--   W^\dagger E_n^\dagger P_jE_mW=\sum_i\langle n|\sigma_{j|i}|m\rangle W^\dagger P_iW\quad\text{for all }j,n,m.
--   $$
--
--   This is a positive, normalized classical–quantum conditional-output criterion; it does not normalize each block separately.
-- source:
--   Approximate recovery with locality and symmetry constraints, arXiv:1806.10324v2, PDF p. 5, §III B, Eqs.(18),(20): exact constrained recovery criterion

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

/-- PDF p.5, Eqs.(18),(20): necessary AND sufficient, including positivity
and total conditional normalization. -/
theorem exact_constrained_recovery [Nonempty H] [Nonempty L] {r : ℕ}
    (s : Sectors H r) (A : J → Mat H) (hA : IsKrausFamily A)
    (hphys : IsPhysicalChannel (sectorProject s) (sectorProject s) (krausApply A))
    (W : Matrix H L ℂ) (hW : Wᴴ * W = 1) :
    PhysicallyCorrectable (sectorProject s) (krausApply A) W ↔
      ChargeStateCondition s A W := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P44

end
