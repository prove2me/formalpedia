-- Prove2me | Theorems.Thm_SolQFTCircuitExact_embedOp_diagonal
-- name    : SolQFTCircuitExact.embedOp_diagonal
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:39:23.553897+00:00
-- url     : https://prove2.me/theorems/f1b7ef7b-a539-59b0-9ff4-c687c0bf07e6
-- title:
--   Embedding a diagonal qubit operator
-- statement:
--   Let $k,n\ge0$, let $d:\{0,1\}^k\to\mathbb C$, and let $e$ be an injection from the $k$ selected wires into $n$ wires. Let $\operatorname{Embed}_e$ extend a $k$-wire operator by the identity on the other wires. Then
--
--   $$
--   \operatorname{Embed}_e(\operatorname{diag}(d))=\operatorname{diag}\bigl(y\mapsto d(y\circ e)\bigr).
--   $$
--
--   This expresses a local diagonal operation as a diagonal operation on the full register.
-- source:
--   Reused exact-QFT proof by kmehltretter82, accepted Prove2Me submission 574f267d-70e8-417a-81da-58cae2f35605 for QAlgorithms.DeWolf.qft_circuit_exact; attribution in Solutions/Section5QFTFoundation.lean, lines 1–3. Exact source: Solutions/Section5QFTFoundation.lean, SolQFTCircuitExact.embedOp_diagonal, lines 161–179.

import Definitions.Def_QAlgorithms_Defs_Fourier
import Mathlib
set_option autoImplicit false
open QAlgorithms
open scoped Matrix BigOperators
namespace SolQFTCircuitExact
end SolQFTCircuitExact
open SolQFTCircuitExact

theorem SolQFTCircuitExact.embedOp_diagonal {k n : ℕ} (d : Qubits k → ℂ) (w : Fin k ↪ Fin n) :
    embedOp (Matrix.diagonal d) w = Matrix.diagonal (fun y => d (y ∘ w)) := by sorry
