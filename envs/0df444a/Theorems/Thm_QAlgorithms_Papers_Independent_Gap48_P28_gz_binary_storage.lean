-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P28_gz_binary_storage
-- name    : QAlgorithms.Papers.Independent.Gap48.P28.gz_binary_storage
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T23:28:09.159876+00:00
-- url     : https://prove2.me/theorems/bb82c8de-a2a3-407e-8e24-d07f9d3bff9a
-- title:
--   Finite Gelfand–Zetlin labels fit in binary registers
-- statement:
--   Let $n,d\ge1$. A Gelfand–Zetlin label is a chain of nonnegative integer partitions $q^{(1)}\prec\cdots\prec q^{(d)}$, where $q^{(r)}$ has at most $r$ parts, every diagram has at most $n$ boxes, and successive rows interlace for the upper-left unitary subgroup tower. Pad every partition to $d$ entries. Encode each entry in $w=\lceil\log_2(n+1)\rceil$ bits, with the most significant bit first. This encoding is injective and uses
--
--   $$
--   d^2\lceil\log_2(n+1)\rceil
--   $$
--
--   binary wires. The wire set is indexed by row, column, and bit position. This supplies the finite register encoding used in the circuit construction; it does not assert compression to the logarithm of an irrep dimension.
-- source:
--   The Quantum Schur Transform: I. Efficient Qudit Circuits, arXiv:quant-ph/0601001v1, PDF p. 11, III B: finite GZ labels and binary storage

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P28

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P28

open scoped Matrix Kronecker ComplexConjugate

/-- PDF p.11, §III B: bounded GZ labels admit the stated binary encoding.
The ceiling restores integer wire counts; this is not the unfulfilled promise
of an encoding in ceil(log₂(dim Q)) qubits. -/
theorem gz_binary_storage (n d : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d) :
    Function.Injective (@gzBinaryCode n d) ∧
    Fintype.card (Fin d × Fin d × Fin (Nat.clog 2 (n + 1))) =
      d ^ 2 * Nat.clog 2 (n + 1) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P28

end
