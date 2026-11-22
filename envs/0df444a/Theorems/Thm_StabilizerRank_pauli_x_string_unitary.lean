-- Prove2me | Theorems.Thm_StabilizerRank_pauli_x_string_unitary
-- name    : StabilizerRank.pauli_x_string_unitary
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-08T01:19:14.552557+00:00
-- url     : https://prove2.me/theorems/127d5cd2-9246-4b62-b6f7-a81830c88a49
-- title:
--   Pauli $X$-strings are unitary
-- statement:
--   Let $x$ be an $n$-bit string and let $X^x$ be the corresponding Pauli $X$-string, the tensor product of Pauli $X$ operators on the qubits where $x$ is true (formally `pauliMatrix x 0`, with trivial $Z$ component). Then $X^x$ is unitary: it acts on the computational basis by the permutation $y \mapsto x \oplus y$ with all phases equal to $1$, so $X^x (X^x)^* = 1$. This is the unitarity half of the fact that $X$-strings are Clifford unitaries, which exhibits every computational-basis state as a stabilizer state.
-- source:
--   Standard Pauli/Clifford theory (e.g. Nielsen-Chuang, Chapter 10); X-string unitarity as needed for the stabilizer-state basis of the StabilizerRank mission.

import Definitions.Def_StabilizerRank

namespace StabilizerRank

theorem pauli_x_string_unitary {n : ℕ} (x : Bits n) :
    pauliMatrix x 0 ∈ Matrix.unitaryGroup (Bits n) ℂ := by sorry

end StabilizerRank
