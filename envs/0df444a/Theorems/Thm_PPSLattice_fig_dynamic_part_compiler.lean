-- Prove2me | Theorems.Thm_PPSLattice_fig_dynamic_part_compiler
-- name    : PPSLattice.fig_dynamic_part_compiler
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:41:32.689596+00:00
-- url     : https://prove2.me/theorems/ce8c8398-2d54-4d67-bb3b-4b1677e0069b
-- title:
--   Claim 4.11 — polynomial-time modular-linear-form compiler for the $(d,h)$ suffix of Figure 1
-- statement:
--   There is a uniform polynomial-time NAND-circuit compiler for the suffix $(d,h)$ of Figure 1, with circuit size bounded by a function $s_{\mathrm{dyn}}(\lambda,N,n,q)$ independent of all hardwired data. For $j\in[\lambda]$,
--   $$d_j=\sum_t s_t(\mathbf B\,\mathbf G^{-1}(\mathbf P))_{tj}-\sum_t s_tP_{tj}+\tilde e_j+tg_j,$$
--   so expansion of the matrix product makes $d_j$ a $\mathbb Z_q$-linear form in the entries of $\mathbf B$, with all coefficients hardwired from $\mathbf s$ and $\mathbf P$. Each such entry is itself a fixed-width binary number decoded from a block of the input $b$. The circuit computes these linear forms, emits their smudged fixed-width encodings as in Remark 4.9, and appends the static bits $h_j=\operatorname{round}_2(tg_j)\oplus\mu_j$. The statement retains explicit polynomial-time computability of both the circuit description and the unary size function.
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission #1347 (manuscript sha256 7f9c493f…), Figure 1 and Remark 4.9, p.22; Claim 4.11, p.22.

import Definitions.Def_PPSLattice_FigParts
open QAlgorithms.Complexity
set_option autoImplicit false

namespace PPSLattice

/-- The suffix `(d,h)` of Figure 1 has a uniform polynomial-time NAND-circuit compiler with a
size bound depending only on `λ,N,n,q`. Only `d` depends on the circuit input; its coordinates
are hardwired `Z_q`-linear forms in the entries decoded from `b`. -/
theorem fig_dynamic_part_compiler :
    ∃ (K : Str → RestrictedDec.Circuit) (sC : ℕ → ℕ → ℕ → ℕ → ℕ),
      FigPartCompilerValid figDynamicOut K sC := by sorry
