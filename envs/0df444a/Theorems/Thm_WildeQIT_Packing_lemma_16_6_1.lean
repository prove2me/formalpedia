-- Prove2me | Theorems.Thm_WildeQIT_Packing_lemma_16_6_1
-- name    : WildeQIT.Packing.lemma_16_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:56:08.04218+00:00
-- url     : https://prove2.me/theorems/24c3b859-1a6e-427b-a949-7ed9c0bb478c
-- title:
--   Non-commutative union bound: $\mathrm{Tr}\{\omega\}-\mathrm{Tr}\{P_L\cdots P_1\omega P_1\cdots P_L\}\le2\sqrt{\sum_i\mathrm{Tr}\{(I-P_i)\omega\}}$
-- statement:
--   **Lemma 16.6.1 (Non-Commutative Union Bound).** Let $\omega$ be a positive semi-definite operator on a finite-dimensional Hilbert space with $\operatorname{Tr}\{\omega\}\le1$, and let $P_1,\dots,P_L$ be Hermitian projectors. Then
--
--   $$\operatorname{Tr}\{\omega\}-\operatorname{Tr}\{P_L\cdots P_1\,\omega\,P_1\cdots P_L\}\le2\sqrt{\sum_{i=1}^{L}\operatorname{Tr}\{(I-P_i)\omega\}}.$$
--
--   It replaces the union bound of probability theory for sequences of non-commuting projective tests, and it is the main tool in the analysis of the sequential decoder.
--
--   **Formalization Note** The projectors are indexed by $\{0,\dots,L-1\}$; $P_1\cdots P_L$ is the product in increasing index order and $P_L\cdots P_1$ the product in decreasing order (both the identity when $L=0$). Projectors are Hermitian idempotents; traces are real parts of complex traces.
--
--   Differences from the source: none.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Lemma 16.6.1, eq. (16.90), p. 499

import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §16.6, Lemma 16.6.1
(Non-Commutative Union Bound), eq. (16.90), p. 499.
-/

open Matrix
open scoped ComplexOrder

namespace WildeQIT.Packing

/-- **Lemma 16.6.1 (Non-Commutative Union Bound)** (Wilde, arXiv:1106.1445v8, eq. (16.90),
p. 499). Let `ω ≥ 0` with `Tr{ω} ≤ 1`, and let `P_1, …, P_L` be Hermitian projectors. Then
`Tr{ω} − Tr{P_L ⋯ P_1 ω P_1 ⋯ P_L} ≤ 2 √(∑_{i=1}^{L} Tr{(I − P_i) ω})`.

**Formalization Note.** Operators are complex matrices indexed by a finite type `n`. The
projectors are `P : Fin L → Matrix n n ℂ` (index base `0`), each a Hermitian idempotent
(`IsStarProjection`). `P_1 ⋯ P_L` is the list product `(List.ofFn P).prod` and `P_L ⋯ P_1` the
product of the reversed list; for `L = 0` both are `I`. Traces are real parts of complex traces
(real for the Hermitian operators involved). -/
theorem lemma_16_6_1 {n : Type} [Fintype n] [DecidableEq n] {L : ℕ} (ω : Matrix n n ℂ) (hω : ω.PosSemidef) (htr : ω.trace.re ≤ 1) (P : Fin L → Matrix n n ℂ) (hP : ∀ i, IsStarProjection (P i)) : ω.trace.re - ((List.ofFn P).reverse.prod * ω * (List.ofFn P).prod).trace.re ≤ 2 * Real.sqrt (∑ i, ((1 - P i) * ω).trace.re) := by sorry

end WildeQIT.Packing
