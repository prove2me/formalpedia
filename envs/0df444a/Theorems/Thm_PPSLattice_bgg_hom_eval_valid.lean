-- Prove2me | Theorems.Thm_PPSLattice_bgg_hom_eval_valid
-- name    : PPSLattice.bgg_hom_eval_valid
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T02:37:47.019905+00:00
-- url     : https://prove2.me/theorems/262463cf-818e-4dec-bdc7-c47b3029f44a
-- title:
--   BGG+ NAND evaluation: exact identity and quadratic-depth norm bound
-- statement:
--   For every prime $q$, dimensions $n,m$ with $n\lceil\log_2q\rceil\le m$, input length $\ell$, matrix $\mathbf B\in\mathbb Z_q^{n\times\ell m}$, single-output NAND circuit $f$ of depth $d$, and $\mathbf x\in\{0,1\}^{\ell}$, the explicit BGG+ algorithms satisfy
--   $$
--   (\mathbf B-\mathbf x^\top\otimes\mathbf G)\mathbf H_{f,\mathbf x}
--   =\mathbf B_f-f(\mathbf x)\mathbf G,
--   \qquad
--   \|\mathbf H_{f,\mathbf x}\|\le m^{2(d+1)}.
--   $$
--   The norm uses centered representatives in $\mathbb Z_q$. The bound is independent of the number of gates. Invalid wire references follow the zero-value convention of the circuit semantics.
--
--   This is the validity half of the homomorphic-computation theorem of §3.1. The induction invariant is $(\mathbf B-\mathbf x^\top\otimes\mathbf G)\mathbf H_w=\mathbf B_w-x_w\mathbf G$ for every input or gate wire. At a NAND gate, $\mathbf G\mathbf G^{-1}(\mathbf B_b)=\mathbf B_b$ gives the algebraic identity, while $0/1$ entries of $\mathbf G^{-1}(\mathbf B_b)$ give the depth-only norm recurrence.
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), §3.1, Homomorphic Computation, properties (1)–(2), pp.16–17; GSW13/BGG+14 NAND evaluation.

import Mathlib
import Definitions.Def_PPSLattice_HomEval_Valid
import Definitions.Def_PPSLattice_BGGHomEval
set_option autoImplicit false

/-- The explicit BGG+ NAND-circuit evaluation algorithms satisfy the two homomorphic-computation
properties, with exponent constant `2`. -/
theorem PPSLattice.bgg_hom_eval_valid : PPSLattice.bggHomEval.Valid 2 := by sorry
