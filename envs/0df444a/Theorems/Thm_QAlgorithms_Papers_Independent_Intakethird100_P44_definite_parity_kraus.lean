-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P44_definite_parity_kraus
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P44.definite_parity_kraus
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:20:23.053298+00:00
-- url     : https://prove2.me/theorems/c0140fe6-5a48-4d7c-be36-8a53ff0ba106
-- title:
--   Definite-parity Kraus representation
-- statement:
--   All Hilbert spaces are finite dimensional and nonzero, and every channel is completely positive and trace preserving on the full matrix algebra. Let $C$ be total parity for a finite spinless-fermion Fock space, and put $\mathcal P=\mathcal Q:X\mapsto(X+CXC)/2$. A channel $\mathcal N$ is physical if $\mathcal Q\mathcal N\mathcal P=\mathcal Q\mathcal N$. A Kraus operator has definite parity when it commutes or anticommutes with $C$. Then
--
--   $$
--   \bigl[\mathcal N\text{ has a normalized definite-parity Kraus representation}\bigr]\Longrightarrow\mathcal N\text{ physical},
--   $$
--   $$
--   \mathcal N\text{ physical}\Longrightarrow\mathcal Q\mathcal N=\mathcal Q\mathcal N\mathcal P\text{ has such a representation}.
--   $$
--
--   The projected channel has the same physical-observable action. Both parity-preserving and parity-flipping Kraus operators are allowed.
-- source:
--   Approximate recovery with locality and symmetry constraints, arXiv:1806.10324v2, PDF p. 3, Proposition 1: definite-parity Kraus representation

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

/-- PDF p.3, Proposition 1. The converse represents the PHYSICALLY
EQUIVALENT projected channel QN, not necessarily N on forbidden coherences. 
Parity correction, PDF p.2 Eq.(1): printed i^(|omega|-1) for Majorana labels;
changed to i^m on 2m ordered modes. Why: the printed four-mode value is
anti-Hermitian with square -I, whereas the source requires parity sectors of
a Hermitian involution. Only this normalization (up to sign) is corrected. -/
theorem definite_parity_kraus {n : ℕ} (f : Fermions n)
    (N : Superop (Fin (2 ^ n)) (Fin (2 ^ n))) (hN : IsChannel N) :
    ((∃ (m : ℕ) (A : Fin m → Mat (Fin (2 ^ n))), IsKrausFamily A ∧
        N = krausApply A ∧ ∀ j, DefiniteParity (totalParity f) (A j)) →
      IsPhysicalChannel (parityProject (totalParity f)) (parityProject (totalParity f)) N) ∧
    (IsPhysicalChannel (parityProject (totalParity f)) (parityProject (totalParity f)) N →
      ∃ (m : ℕ) (A : Fin m → Mat (Fin (2 ^ n))), IsKrausFamily A ∧
        parityProject (totalParity f) ∘ N = krausApply A ∧
        ∀ j, DefiniteParity (totalParity f) (A j)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P44

end
