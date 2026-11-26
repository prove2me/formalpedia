-- Prove2me | Theorems.Thm_SolQFTCircuitExact_qftQubits_step
-- name    : SolQFTCircuitExact.qftQubits_step
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:41:36.877713+00:00
-- url     : https://prove2.me/theorems/487c860f-fb83-5190-8533-9b5d125dd3ae
-- title:
--   Entrywise recursion for the qubit quantum Fourier transform
-- statement:
--   For $n\ge0$ let $F_n$ be the $n$-qubit Fourier matrix with most-significant-bit-first indexing, positive exponential sign, and normalization $2^{-n/2}$. Let $H$ be the Hadamard matrix. For $(n+1)$-bit strings $j,k$, write $j'=(j_1,\ldots,j_n)$ and $k'=(k_0,\ldots,k_{n-1})$, and interpret bits as integers $0$ or $1$. Then
--
--   $$
--   (F_{n+1})_{j,k}=H_{j_0,k_n}\left(\prod_{m=0}^{n-1}\exp\!\left(\frac{2\pi i\,j_{m+1}k_n}{2^{m+2}}\right)\right)(F_n)_{j',k'}.
--   $$
--
--   This gives the matrix-entry decomposition underlying recursive exact QFT circuits.
-- source:
--   Reused exact-QFT proof by kmehltretter82, accepted Prove2Me submission 574f267d-70e8-417a-81da-58cae2f35605 for QAlgorithms.DeWolf.qft_circuit_exact; attribution in Solutions/Section5QFTFoundation.lean, lines 1–3. Exact source: Solutions/Section5QFTFoundation.lean, SolQFTCircuitExact.qftQubits_step, lines 508–581.

import Definitions.Def_QAlgorithms_Defs_Fourier
import Mathlib
set_option autoImplicit false
open QAlgorithms
open scoped Matrix BigOperators
namespace SolQFTCircuitExact
end SolQFTCircuitExact
open SolQFTCircuitExact

theorem SolQFTCircuitExact.qftQubits_step (n : ℕ) (j k : Qubits (n + 1)) :
    hadamard (j 0) (k (Fin.last n)) *
      ((∏ m : Fin n,
          if Fin.tail j m && k (Fin.last n) then
            Complex.exp (2 * Real.pi * Complex.I / (2 : ℂ) ^ ((m : ℕ) + 2))
          else 1) *
        qftQubits n (Fin.tail j) (Fin.init k)) =
      qftQubits (n + 1) j k := by sorry
