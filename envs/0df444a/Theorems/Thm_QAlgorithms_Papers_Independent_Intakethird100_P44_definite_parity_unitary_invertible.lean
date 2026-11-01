-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P44_definite_parity_unitary_invertible
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P44.definite_parity_unitary_invertible
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:25:27.866989+00:00
-- url     : https://prove2.me/theorems/1a299b52-fceb-4f80-affb-f26be95ba562
-- title:
--   Physical inversion of definite-parity unitary noise
-- statement:
--   All Hilbert spaces are finite dimensional and nonzero, and every channel is completely positive and trace preserving on the full matrix algebra. Let $C$ be total fermionic parity and $\mathcal P(X)=(X+CXC)/2$. Let $U$ be unitary and have definite parity, $UC=CU$ or $UC=-CU$. Then $\mathcal N=\operatorname{Ad}_U$ and $\mathcal R=\operatorname{Ad}_{U^\dagger}$ are physical CPTP channels and
--
--   $$
--   \mathcal R\mathcal N(X)=X\quad\text{for every matrix }X.
--   $$
--
--   In particular the inverse physically corrects the noise, including when $U$ flips total parity.
-- source:
--   Approximate recovery with locality and symmetry constraints, arXiv:1806.10324v2, PDF p. 6, §III C: physical invertibility of definite-parity unitary noise

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

/-- PDF p.6, Section III C: a definite-parity unitary and its inverse are
physical; parity-flipping unitaries are included. 
Parity correction, PDF p.2 Eq.(1): printed i^(|omega|-1) for Majorana labels;
changed to i^m on 2m ordered modes. Why: the printed four-mode value is
anti-Hermitian with square -I, whereas the source requires parity sectors of
a Hermitian involution. Only this normalization (up to sign) is corrected. -/
theorem definite_parity_unitary_invertible {n : ℕ} (f : Fermions n)
    (U : Mat (Fin (2 ^ n))) (hU : Uᴴ * U = 1) (hUU : U * Uᴴ = 1)
    (hparity : DefiniteParity (totalParity f) U) :
    IsChannel (conjSuperop U) ∧ IsChannel (conjSuperop Uᴴ) ∧
    IsPhysicalChannel (parityProject (totalParity f)) (parityProject (totalParity f))
      (conjSuperop U) ∧
    IsPhysicalChannel (parityProject (totalParity f)) (parityProject (totalParity f))
      (conjSuperop Uᴴ) ∧
    ∀ X, conjSuperop Uᴴ (conjSuperop U X) = X := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P44

end
