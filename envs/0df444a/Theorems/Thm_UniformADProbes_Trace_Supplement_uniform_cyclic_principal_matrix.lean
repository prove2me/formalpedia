-- Prove2me | Theorems.Thm_UniformADProbes_Trace_Supplement_uniform_cyclic_principal_matrix
-- name    : UniformADProbes.Trace.Supplement.uniform_cyclic_principal_matrix
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:20:52.071394+00:00
-- url     : https://prove2.me/theorems/e943aefb-f83d-46b3-bba0-8c9b6783fb3e
-- title:
--   Theorem A.2 — Uniform cyclic principal matrix
-- statement:
--   There are absolute positive integer $c$ and nonnegative integer $k$, chosen before $N$, such that for every $N\ge1$ the defined charged constructor emits a valid original-order integer matrix circuit $C_N$. Its formal polynomial is a finite sum of Hermitian squares. It returns $1$ at $N=1$; for $N\ge2$ every stored register has formal degree at most $2(4N-3)(N-1)$. The instruction count, signed bit length of every scalar literal, signed bit length of every matrix entry in every register and of the final trace on every permitted tree, and the charged binary construction cost are each bounded by $c(N+1)^k$.
--
--   For every finite connected simple tree $T$ of any order $n\le N$, let $B=C_N(A_T,D_T)$ be its real evaluation and let $\mathcal M_T$ be its principal module from the all-ones vector. Then
--   $$
--   B\succeq0,\qquad \operatorname{im}B=\mathcal M_T,\qquad
--   \operatorname{span}_{\mathbb R}\{\mathbf1,B\mathbf1,\ldots,B^{N-1}\mathbf1\}=\mathcal M_T.
--   $$
--   The sum-of-squares claim is a polynomial identity $C_N=\sum_{q\in Q}qq^*$, separate from evaluated positive semidefiniteness. All gates use the original matrix space; there is no determinant, inverse, rank, adjugate or trace oracle. This is a companion to Theorem 1.1, independent of its trace encoding, supported by Lemma A.1.
--
--   **Formalization Note** The fixed emitter expands equations (13), (16) and (17), including homogeneous Bird determinants; polynomial-time construction is measured by the published builder and charged binary arithmetic. A common uniform polynomial envelope expresses all polynomial clauses of the source without selecting instance-dependent constants. Bird uses $O(k_0^4)$ operations for each determinant of order $k_0$ and there are $O(N^2)$ such determinants; the entry bounds follow the coefficient estimate on printed p.14. The detailed growth and charge analysis is in MODERATION_NOTES.md.
--
--   Differences from the source:
--   - encoding: a deterministic polynomial-time construction with polynomial size and bit complexity → the fixed charged emitter of equations (13), (16), (17), with a common bound c(N+1)^k and c,k before N; reason: finitely many uniform polynomial resource bounds have a common polynomial envelope; literal, every-register entry, final trace and construction cost clauses are all retained
--   - encoding: positive semidefinite C_N, image and cyclic span on every tree → real cast of the emitted integer output, LinearMap.range and real Submodule.span over Fin N; reason: integer circuit evaluation followed by the cast is real polynomial evaluation; Fin N includes exactly the powers 0 through N-1
--   - encoding: formal degree at most 2(4N-3)(N-1) for N at least 2 → the same bound on every stored register using syntactic degree propagation; reason: formal circuit degree is the maximum gate degree and ignores algebraic cancellation
-- source:
--   Zhipeng Lu, Uniform adjacency-degree probes from differential rigidity, STOC 2027 submission #25 (October 2026), Theorem A.2, p. 13 (PDF p. 14); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/25.pdf

import Definitions.Def_UniformADProbes_Trace_Supplement_cyclic_construction

set_option autoImplicit false

namespace UniformADProbes.Trace.Supplement

theorem uniform_cyclic_principal_matrix :
    ∃ c k : ℕ, 0 < c ∧ ∀ N : ℕ, 1 ≤ N →
      let C := cyclicCircuit N
      C.Valid ∧
      (∃ Q : List NCPoly, C.denotation = (Q.map fun q => q * adjoint q).sum) ∧
      (N = 1 → C.denotation = 1) ∧
      (2 ≤ N → C.DegreeBound (2 * (4 * N - 3) * (N - 1))) ∧
      C.code.size ≤ c * (N + 1)^k ∧
      C.LiteralBound (c * (N + 1)^k) ∧
      C.EntryBound N (c * (N + 1)^k) ∧
      cyclicCost N ≤ c * (N + 1)^k ∧
      (∀ n : ℕ, n ≤ N → ∀ T : SimpleGraph (Fin n), T.IsTree →
        let B := realMatrix (outputValue C (adjacency T) (degreeMatrix T))
        B.PosSemidef ∧
        LinearMap.range B.mulVecLin = treeModule T ∧
        Submodule.span ℝ (Set.range fun j : Fin N =>
          (B^j.val).mulVec (ones n)) = treeModule T) := by sorry

end UniformADProbes.Trace.Supplement
