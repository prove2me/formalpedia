-- Prove2me | Theorems.Thm_PPSLattice_fig_part_compiler_join
-- name    : PPSLattice.fig_part_compiler_join
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:43:17.782943+00:00
-- url     : https://prove2.me/theorems/ab53d964-f1a4-4fd4-9a2b-77d471ae8f1d
-- title:
--   Claim 4.11 — sequential append combines two valid output-part compilers
-- statement:
--   Let $K_1,K_2$ be valid polynomial-time circuit compilers for two output parts $F,G$ of Figure 1, with respective size functions $s_1,s_2$. Then the circuit that evaluates $K_1$ and $K_2$ sequentially on their common input and appends the two output lists computes $F\Vert G$, has at most $s_1+s_2$ gates, and satisfies the same uniform polynomial-time obligations. Formally, `joinFigCompiler K₁ K₂` uses the input length parsed by `figInputLen` and `appendCircuit` shifts all internal wires of the second circuit to fresh indices. The conclusion includes polynomial-time computability of the combined circuit description and of $1^{s_1+s_2}$, exact evaluation on every prescribed-length input, and the uniform size bound.
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission #1347 (manuscript sha256 7f9c493f…), Figure 1 and Claim 4.11, p.22; standard sequential composition of Boolean circuits used by the size claim.

import Definitions.Def_PPSLattice_FigParts
open QAlgorithms.Complexity
set_option autoImplicit false

namespace PPSLattice

/-- Sequential evaluation and output concatenation preserve the uniform Figure-1 part-compiler
contract. In particular, both `PolyTimeOn` obligations and exact evaluation are preserved. -/
theorem fig_part_compiler_join
    (F G : FigFun) (K₁ K₂ : Str → RestrictedDec.Circuit)
    (s₁ s₂ : ℕ → ℕ → ℕ → ℕ → ℕ) :
    FigPartCompilerValid F K₁ s₁ → FigPartCompilerValid G K₂ s₂ →
      FigPartCompilerValid (figPartAdd F G) (joinFigCompiler K₁ K₂) (joinFigSize s₁ s₂) := by sorry
