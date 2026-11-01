-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P44_majorana_poisoning_not_correctable
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P44.majorana_poisoning_not_correctable
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:26:19.847195+00:00
-- url     : https://prove2.me/theorems/7fccd2a0-97bb-43b5-a742-55c72be32c85
-- title:
--   Two free-Majorana jumps obstruct physical recovery
-- statement:
--   All Hilbert spaces are finite dimensional and nonzero, and every channel is completely positive and trace preserving on the full matrix algebra. Consider $2n$ Majorana operators $w_a=w_a^\dagger$ on the $2^n$-dimensional Fock space, satisfying $\{w_a,w_b\}=2\delta_{ab}I$. There are $2k>0$ free modes in cyclic order, with even-length intervals $I_j$ of nearest-neighbor paired modes between consecutive free modes. The isometry $W$ encodes all $2^k$ free-mode states and initializes each paired fermion in its specified vacuum; its range projector is the product of the paired-mode vacuum projectors. Write $C$ for total parity and $\mathcal P(X)=(X+CXC)/2$. Suppose $2k>2$, and define
--
--   $$
--   \mathcal N(X)=\tfrac12\bigl(w_{\omega_1}Xw_{\omega_1}+w_{\omega_2}Xw_{\omega_2}\bigr),\qquad M=iw_{\omega_2}w_{\omega_3}.
--   $$
--
--   Then $\mathcal N$ is physical and CPTP, $\mathcal N^\dagger(M)=0$, and $M$ commutes with $C$ and $WW^\dagger$. Its logical compression $W^\dagger MW$ is not scalar. There is no physical CPTP recovery satisfying
--
--   $$
--   \mathcal R\mathcal N(WXW^\dagger)=\mathcal P(WXW^\dagger)\quad\text{for every logical matrix }X.
--   $$
--
--   Thus this poisoning noise destroys recoverable physical logical information; no numerical optimum is claimed.
-- source:
--   Approximate recovery with locality and symmetry constraints, arXiv:1806.10324v2, PDF p. 6, §III C: two unpaired-Majorana jumps prevent physical recovery

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

/-- PDF pp.6--7, Section III C: physical but uncorrectable poisoning when
there are more than two free Majoranas; the stated physical logical witness
is annihilated. No numerical optimal-fidelity estimate is asserted. 
Parity correction, PDF p.2 Eq.(1): printed i^(|omega|-1) for Majorana labels;
changed to i^m on 2m ordered modes. Why: the printed four-mode value is
anti-Hermitian with square -I, whereas the source requires parity sectors of
a Hermitian involution. Only this normalization (up to sign) is corrected. -/
theorem majorana_poisoning_not_correctable {n k : ℕ}
    (f : Fermions n) (r : RingLayout n k) (code : RingCode f r) (hk : 2 < 2 * k) :
    let a : Fin (2 * k) := ⟨1, by omega⟩
    let b : Fin (2 * k) := ⟨2, by omega⟩
    let M := Complex.I • (f.w (r.free a) * f.w (r.free b))
    IsChannel (poisoning f r) ∧
    IsPhysicalChannel (parityProject (totalParity f)) (parityProject (totalParity f))
      (poisoning f r) ∧
    operatorTraceDual (poisoning f r) M = 0 ∧
    M * totalParity f = totalParity f * M ∧
    M * (code.W * code.Wᴴ) = (code.W * code.Wᴴ) * M ∧
    (¬ ∃ z : ℂ, code.Wᴴ * M * code.W = z • (1 : Mat (Fin (2 ^ k)))) ∧
    ¬ PhysicallyCorrectable (parityProject (totalParity f)) (poisoning f r) code.W := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P44

end
