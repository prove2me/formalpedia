-- Prove2me | Theorems.Thm_PPSLattice_fig_compiler_size_polynomial
-- name    : PPSLattice.fig_compiler_size_polynomial
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:49:06.857256+00:00
-- url     : https://prove2.me/theorems/8ee6a6e2-ace3-4be9-8579-ee8749950236
-- title:
--   Claim 4.11 — polynomial output length of the size machine gives the uniform size exponent
-- statement:
--   If `FigCompilerValid K sC` holds, then there is one constant $c$ such that, for every $\lambda,N,n,q$,
--   $$s_C(\lambda,N,n,q)\le(\lambda+n+n\lceil\log_2q\rceil+\lceil\log_2N\rceil+\lceil\log_2q\rceil+2)^c.$$
--   Indeed, the second `PolyTimeOn` clause of `FigCompilerValid` supplies one TM2 machine that maps $\operatorname{tup}(1^\lambda,\operatorname{bin}N,1^n,\operatorname{bin}q)$ to $1^{s_C}$ within a polynomial number of steps in the length of that tuple. A Turing machine cannot write an output longer than its running time; the tuple has length linear in $\lambda,n$ and the binary lengths of $N,q$. These binary lengths are bounded by the corresponding ceiling logarithms up to the fixed additive slack already present in the displayed polynomial. This lemma isolates the general TM2 output-length argument needed for Claim 4.11.
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission #1347 (manuscript sha256 7f9c493f…), Claim 4.11, p.23; Definitions.Def_PPSLattice_FigCompilerValid (uniform polynomial-time size machine).

import Mathlib
import Definitions.Def_PPSLattice_FigCompilerValid
open QAlgorithms.Complexity
set_option autoImplicit false

namespace PPSLattice

/-- A valid Figure-1 compiler has a single polynomial exponent bounding its size function. This is
the output-length consequence of the `PolyTimeOn` obligation for the size machine. -/
theorem fig_compiler_size_polynomial (K : Str → RestrictedDec.Circuit)
    (sC : ℕ → ℕ → ℕ → ℕ → ℕ) :
    FigCompilerValid K sC → ∃ c : ℕ, ∀ lam N n q : ℕ,
      sC lam N n q ≤ (lam + n + n * Nat.clog 2 q + Nat.clog 2 N + Nat.clog 2 q + 2) ^ c := by sorry
