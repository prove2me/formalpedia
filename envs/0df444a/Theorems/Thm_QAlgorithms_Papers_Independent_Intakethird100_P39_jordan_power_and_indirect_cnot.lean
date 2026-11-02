-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P39_jordan_power_and_indirect_cnot
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P39.jordan_power_and_indirect_cnot
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:47:27.739476+00:00
-- url     : https://prove2.me/theorems/e8969c22-c501-4d84-a122-faa48b114a6a
-- title:
--   Jordan powers and power-of-two indirect CNOT
-- statement:
--   For $\ell\ge0$, let $J$ be the $(\ell+1)\times(\ell+1)$ lower bidiagonal matrix with ones on the diagonal and first lower diagonal. Over the natural numbers,
--
--   $$(J^\ell)_{ij}=\begin{cases}\binom{\ell}{i-j},&j\le i,\\0,&i<j.\end{cases}$$
--
--   If $\ell=2^p$ with $p\ge1$, reduction modulo two gives
--
--   $$J^\ell=I+E_{\ell,0}.$$
--
--   Consequently, $\ell$ repetitions of either neighboring CNOT sweep (targets in increasing order, or in decreasing order) apply the endpoint CNOT: $x_\ell\mapsto x_\ell\oplus x_0$, with all other bits fixed, for every input bit string. Thus both Fig. 12 circuits restore every borrowed intermediate bit. Equality of these basis permutations gives the corresponding exact quantum circuit identities by linear extension.
-- source:
--   Quantum CISC Compilation by Optimal Control and Scalable Assembly of Complex Instruction Sets beyond Two-Qubit Gates, arXiv:0712.3227v2, PDF p. 13, Jordan power and power-of-two indirect CNOT, Eqs. (36)–(38), Fig. 12

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P39

namespace QAlgorithms.Papers.Independent.Intakethird100.P39

open scoped BigOperators

/-- PDF pp.13-14, Eqs. (36)-(38) and both Fig.12 identities: the natural
binomial formula and its binary reduction, together with the exact actions
of both repeated neighboring sweeps. Intermediate bits are borrowed,
never initialized. The bit identities extend linearly to quantum registers. -/
theorem jordan_power_and_indirect_cnot :
    (∀ (ell : ℕ) (i j : Fin (ell + 1)),
      (jordanMatrix ℕ ell ^ ell) i j =
        if j.val ≤ i.val then Nat.choose ell (i.val - j.val) else 0) ∧
    (∀ p : ℕ, 1 ≤ p →
      jordanMatrix (ZMod 2) (2 ^ p) ^ (2 ^ p) = endpointMatrix (2 ^ p) ∧
      ∀ x : Qubits (2 ^ p + 1),
        (ascendingSweep (2 ^ p))^[2 ^ p] x = endpointCnot (2 ^ p) x ∧
        (descendingSweep (2 ^ p))^[2 ^ p] x = endpointCnot (2 ^ p) x) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P39
