-- Prove2me | Theorems.Thm_PPSLattice_fig_static_part_compiler
-- name    : PPSLattice.fig_static_part_compiler
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:38:17.139907+00:00
-- url     : https://prove2.me/theorems/fb66f427-b270-4518-996a-dc34c3300291
-- title:
--   Claim 4.11 — polynomial-time compiler for the static $(c,P)$ prefix of Figure 1
-- statement:
--   There is a polynomial-time NAND-circuit compiler for the hardwired output prefix $(c,P)$ of Figure 1. Here
--   $$c=\mathbf s^\top\bigl(\mathbf A-\operatorname{encvec}(i)^\top\otimes\mathbf G\bigr)+\mathbf e$$
--   is computed from the hardwired data, and both $c$ and the row-major encoding of $P$ use the smudged fixed-width encoding of Remark 4.9. The compiler ignores the circuit input $b$ and emits this static string. Its circuit has at most $s_{\mathrm{pre}}(\lambda,N,n,q)$ gates, its description and $1^{s_{\mathrm{pre}}}$ are computable in polynomial time in the same encodings as Claim 4.11, and its evaluation is exactly `figPreOut` for every input $b$ of the prescribed length. This isolates the static-output arithmetic and encoding work from the input-dependent linear forms.
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission #1347 (manuscript sha256 7f9c493f…), Figure 1 and Remark 4.9, p.22; Claim 4.11, p.22.

import Definitions.Def_PPSLattice_FigParts
open QAlgorithms.Complexity
set_option autoImplicit false

namespace PPSLattice

/-- The hardwired prefix `(c,P)` of Figure 1 has a uniform polynomial-time NAND-circuit compiler
with a size bound depending only on `λ,N,n,q`. The part-compiler contract includes both `PolyTimeOn`
obligations, the uniform size bound, and exact evaluation on every encoded matrix `B`. -/
theorem fig_static_part_compiler :
    ∃ (K : Str → RestrictedDec.Circuit) (sC : ℕ → ℕ → ℕ → ℕ → ℕ),
      FigPartCompilerValid figPreOut K sC := by sorry
