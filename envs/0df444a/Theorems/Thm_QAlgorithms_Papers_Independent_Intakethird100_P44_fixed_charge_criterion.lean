-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P44_fixed_charge_criterion
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P44.fixed_charge_criterion
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:24:30.744198+00:00
-- url     : https://prove2.me/theorems/43f05260-cd3f-4c14-a11a-0fcac998bfd5
-- title:
--   Fixed-charge correction criterion
-- statement:
--   All Hilbert spaces are finite dimensional and nonzero, and every channel is completely positive and trace preserving on the full matrix algebra. Let $P_1,\ldots,P_r$ be nonzero orthogonal Hermitian sector projectors summing to $I$, let $C=\sum_i c_iP_i$ have pairwise distinct real eigenvalues, and put $\mathcal P(X)=\sum_iP_iXP_i$. Let $\mathcal N(X)=\sum_nE_nXE_n^\dagger$ have a finite normalized Kraus family and satisfy $\mathcal P\mathcal N\mathcal P=\mathcal P\mathcal N$. Let $W$ be an isometry from a nonzero logical space. Correctability means existence of a CPTP $\mathcal R$ with $\mathcal P\mathcal R\mathcal P=\mathcal P\mathcal R$ and $\mathcal R\mathcal N(WXW^\dagger)=\mathcal P(WXW^\dagger)$ for every logical matrix $X$. Suppose $P_{i_0}W=W$ for some fixed sector $i_0$. The code is correctable if and only if there is a complex array $(c_{jnm})$ with
--
--   $$
--   W^\dagger E_n^\dagger P_jE_mW=c_{jnm}W^\dagger W\quad\text{for all }j,n,m.
--   $$
--
--   Here $W^\dagger W$ is the logical identity. Fixed charge implies code-projector invariance, so the preceding sufficiency statement applies.
-- source:
--   Approximate recovery with locality and symmetry constraints, arXiv:1806.10324v2, PDF p. 6, §III B, Eq.(22): fixed-charge simplification

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

/-- PDF p.6, Eq.(22), together with the immediately preceding sufficiency
statement. W†W is the LOGICAL identity, and coefficients are uniform. -/
theorem fixed_charge_criterion [Nonempty H] [Nonempty L] {r : ℕ}
    (s : Sectors H r) (A : J → Mat H) (hA : IsKrausFamily A)
    (hphys : IsPhysicalChannel (sectorProject s) (sectorProject s) (krausApply A))
    (W : Matrix H L ℂ) (hW : Wᴴ * W = 1)
    (i0 : Fin r) (hcharge : s.P i0 * W = W) :
    PhysicallyCorrectable (sectorProject s) (krausApply A) W ↔
      ∃ c : Fin r → J → J → ℂ, ∀ j n m,
        Wᴴ * (A n)ᴴ * s.P j * A m * W = c j n m • (Wᴴ * W) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P44

end
