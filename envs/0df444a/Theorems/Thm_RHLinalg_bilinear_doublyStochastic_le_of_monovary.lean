-- Prove2me | Theorems.Thm_RHLinalg_bilinear_doublyStochastic_le_of_monovary
-- name    : RHLinalg.bilinear_doublyStochastic_le_of_monovary
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:37:52.181323+00:00
-- url     : https://prove2.me/theorems/d9ba7a0f-6941-45dd-abee-53ed7428529f
-- title:
--   Doubly stochastic averaging of a monovarying bilinear form: $\sum_{k,l} a_k S_{kl} b_l \le \sum_k a_k b_k$
-- statement:
--   Let $n$ be a finite index type, let $a, b : n \to \mathbb{R}$ be families that *monovary* (Mathlib's `Monovary a b`: whenever $b_i < b_j$ one has $a_i \le a_j$ — i.e. $a$ and $b$ are similarly ordered), and let $S$ be an $n \times n$ real matrix that is doubly stochastic (nonnegative entries, all row sums and column sums equal to $1$).
--
--   **Statement.**
--   $$\sum_{k}\sum_{l} a_k\, S_{kl}\, b_l \;\le\; \sum_{k} a_k b_k.$$
--
--   The proof is the classical combination of the Birkhoff–von Neumann theorem (a doubly stochastic matrix is a convex combination of permutation matrices) with the rearrangement inequality: for each permutation $\sigma$, $\sum_k a_k b_{\sigma(k)} \le \sum_k a_k b_k$ since $a$ and $b$ are similarly ordered, and averaging over the Birkhoff weights gives the claim.
--
--   In the module `Zeta23.LinAlg.VonNeumann` this is the core combinatorial step behind von Neumann's trace inequality `RHLinalg.vonNeumann_trace_ineq`, part of the linear-algebra toolkit for the matrix-variational (rank–trace) portion of the zeta-zeros argument.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/LinAlg/VonNeumann.lean#L137-L165

import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Matrix.PosDef
import Definitions.Def_Zeta23_LinAlg_PosIndex
import Definitions.Def_Zeta23_LinAlg_VonNeumann

open Matrix Finset
open scoped ComplexOrder
open RHLinalg
variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem RHLinalg.bilinear_doublyStochastic_le_of_monovary {a b : n → ℝ}
    (hab : Monovary a b) {S : Matrix n n ℝ} (hS : S ∈ doublyStochastic ℝ n) :
    ∑ k, ∑ l, a k * S k l * b l ≤ ∑ k, a k * b k := by sorry
