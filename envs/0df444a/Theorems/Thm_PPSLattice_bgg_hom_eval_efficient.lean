-- Prove2me | Theorems.Thm_PPSLattice_bgg_hom_eval_efficient
-- name    : PPSLattice.bgg_hom_eval_efficient
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T02:39:43.563593+00:00
-- url     : https://prove2.me/theorems/8066b842-6c9d-4e9b-a0ba-99db0a9c747b
-- title:
--   BGG+ NAND evaluation is deterministic polynomial time
-- statement:
--   There are deterministic polynomial-time string machines computing the two explicit BGG+ evaluation algorithms. On input consisting of $q$ in binary, $1^n,1^m,1^\ell$, the row-major encoding of $\mathbf B$, and the circuit description, the first machine outputs the encoding of $\mathbf B_f$; with $\mathbf x$ as an additional input, the second outputs the encoding of $\mathbf H_{f,\mathbf x}$.
--
--   The machine traverses the straight-line circuit once. Each gate performs one column-wise binary decomposition, one matrix product with the resulting $0/1$ matrix, and linear matrix operations, followed by selection of the designated output wire. Hence both running time and output length are polynomial in the description length of the input.
--
--   This is the efficiency half of the homomorphic-computation assertion of §3.1.
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), §3.1, Homomorphic Computation, p.16 ('two deterministic polynomial-time algorithms').

import Mathlib
import Definitions.Def_PPSLattice_HomEval_Efficient
import Definitions.Def_PPSLattice_BGGHomEval
set_option autoImplicit false

/-- Both explicit BGG+ NAND-circuit evaluation algorithms are deterministic polynomial-time
computations on the platform's binary encodings. -/
theorem PPSLattice.bgg_hom_eval_efficient : PPSLattice.bggHomEval.Efficient := by sorry
