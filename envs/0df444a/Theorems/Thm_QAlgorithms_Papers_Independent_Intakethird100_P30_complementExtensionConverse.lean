-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P30_complementExtensionConverse
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P30.complementExtensionConverse
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:45:09.003893+00:00
-- url     : https://prove2.me/theorems/2a33a466-80ed-4e95-870f-aa0f76e06532
-- title:
--   III D: complement extension and converse, (19)
-- statement:
--   For a nonempty code set $C\subseteq\{0,1\}^n$, allowing $n=0$, define
--
--   $$E(C)=\{0c:c\in C\}\ \cup\ \{1\overline c:c\in C\}.$$
--
--   The two blocks are disjoint, so $|E(C)|=2|C|$, and $E(C)$ is closed under bitwise complementation. Conversely let $D$ be a nonempty complement-closed code of positive length $n+1$, and construct its first-coordinate-zero tail code
--
--   $$C_D=\{c:0c\in D\}.$$
--
--   Then $C_D$ is nonempty and $D=E(C_D)$, hence $|D|=2|C_D|$. Fixing the existing first coordinate gives equality of unordered sets, and therefore also the source's representation up to equivalence. The tail may have length zero; no threshold comparison is asserted.
--
--   More generally, replacing the lower tail set by a coordinate permutation and fixed XOR translation of $C$ defines the source’s broader extension. The identity permutation with the all-one translation recovers $E(C)$ exactly.
-- source:
--   Numerical evidence for bound secrecy from two-way post-processing in quantum key distribution, arXiv:1612.07734v2, PDF p. 7, III D: complement extension and converse, (19)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P30

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P30

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J K L A B : Type}

variable [Fintype I] [Fintype J] [Fintype K] [Fintype L]

variable [Fintype A] [Fintype B]

/-- PDF p.7, (19): forward construction and its converse, permitting a zero-length tail.
Exact equality here fixes the existing first coordinate and forgets enumeration. -/
theorem complementExtensionConverse {n : ℕ} :
    (∀ C : Finset (Qubits n),
      twistedExtension C (Equiv.refl _) (fun _ => true) = complementExtension C) ∧
    (∀ C : Finset (Qubits n), C.Nonempty →
      (complementExtension C).card = 2 * C.card ∧ ComplementClosed (complementExtension C)) ∧
    (∀ D : Finset (Qubits (n + 1)), D.Nonempty → ComplementClosed D →
      (zeroTail D).Nonempty ∧ D = complementExtension (zeroTail D) ∧
      D.card = 2 * (zeroTail D).card) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P30

end
