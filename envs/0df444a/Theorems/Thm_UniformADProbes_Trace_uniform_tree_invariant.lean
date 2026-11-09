-- Prove2me | Theorems.Thm_UniformADProbes_Trace_uniform_tree_invariant
-- name    : UniformADProbes.Trace.uniform_tree_invariant
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:50:55.249983+00:00
-- url     : https://prove2.me/theorems/26ce5934-c37c-444c-a90e-e2e5c5ee5aa8
-- title:
--   Theorem 1.1 — A uniform linear-degree tree invariant, all clauses
-- statement:
--   For each integer $N\ge1$, the defined deterministic constructor takes only $N$ and emits a valid original-order matrix circuit whose formal polynomial is exactly the defined $p_N\in\mathbb Z\langle x,y\rangle$. This polynomial is formally self-adjoint. For any finite nonempty connected simple trees $T,T'$ of orders at most $N$, including different orders,
--   $$T\cong T'\quad\Longleftrightarrow\quad
--   \operatorname{tr}p_N(A_T,D_T)=\operatorname{tr}p_N(A_{T'},D_{T'}).$$
--   Writing $\ell_N=\lceil\log_2(N+1)\rceil$, the same constructor satisfies all the following uniform bounds:
--   $$\begin{aligned}
--   \#\text{stored instructions}&\le100N^2,\\
--   \text{formal degree of every register}&\le3N-2,\\
--   \text{signed bits of each prescribed integer literal}&\le20N\ell_N,\\
--   \text{signed bits of every stored matrix entry and the final trace}&\le100N^5\ell_N,\\
--   \text{charged binary construction cost}&\le10^8(N+1)^{12}.
--   \end{aligned}$$
--   The entry and trace bound quantifies over every permitted tree and every register, in its original order. Constants are fixed numerals, independent of $N$, the input order, the tree, and the register. The only scalar readout is the final trace. The singleton case returns identity.
--
--   This states every clause of the source theorem: classification in both directions, formal self-adjointness, uniformity, quadratic shared size, exact linear degree, literal size, intermediate and output size, and polynomial bit construction time.
--
--   **Formalization Note** The emitter uses $12(M-1)$ probe instructions, at most $10N$ distance instructions, $4M$ scalar-power instructions, $8M$ Horner instructions, and constant overhead; $M=N(N+1)/2$. The source norm estimates with $R=(3N^3)^{N-1}$ and $b_N=2N^2R^2+1$ bound each entry and trace by $8N^3M^2R^2b_N^{3M^2}$. The binary estimates and conservative list-copy charges give the displayed numerical envelopes; their derivations are recorded in the moderation notes. Arbitrary real evaluated inputs receive no binary-size bound.
--
--   Differences from the source:
--   - encoding: finite nonempty trees of every order at most N → simple trees on Fin n and Fin m, independently quantified with n,m ≤ N (nonemptiness is part of IsTree); reason: labelling covers every finite tree and imposes no same-order restriction
--   - encoding: a deterministic polynomial-time construction and simultaneous O-bounds → the explicit charged emitter of equation (12), bounds 100N², 20N ceil(log₂(N+1)), 100N⁵ ceil(log₂(N+1)), and 10⁸(N+1)¹²; reason: fixed binary encoding, schoolbook arithmetic, and conservative table-copy semantics realize the source resource rates with absolute constants
--   - encoding: the circuit has formal degree at most 3N − 2 → every stored register has syntactic degree at most 3N − 2; reason: the formal degree of a circuit is the maximum over its gates, propagated without cancellation; the exact bound 3N − 2 is kept
-- source:
--   Zhipeng Lu, Uniform adjacency-degree probes from differential rigidity, STOC 2027 submission #25 (October 2026), Theorem 1.1; §3 equations (10)–(12) and correctness/resource proof, p. 1, 9–10 (PDF p. 2, 10–11); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/25.pdf

import Definitions.Def_UniformADProbes_Trace_circuits

set_option autoImplicit false

namespace UniformADProbes.Trace

theorem uniform_tree_invariant :
    ∀ N : ℕ, 1 ≤ N →
      let C := invariantCircuit N
      C.Valid ∧
      C.denotation = packedPoly N ∧
      adjoint (packedPoly N) = packedPoly N ∧
      C.code.size ≤ 100 * N^2 ∧
      C.DegreeBound (3 * N - 2) ∧
      C.LiteralBound (20 * N * Nat.clog 2 (N + 1)) ∧
      C.EntryBound N (100 * N^5 * Nat.clog 2 (N + 1)) ∧
      constructionCost N ≤ 100000000 * (N + 1)^12 ∧
      (∀ n m : ℕ, n ≤ N → m ≤ N →
        ∀ T : SimpleGraph (Fin n), ∀ T' : SimpleGraph (Fin m),
        T.IsTree → T'.IsTree →
        (Nonempty (T ≃g T') ↔
          Matrix.trace (polyEval (adjacency T) (degreeMatrix T) (packedPoly N)) =
          Matrix.trace (polyEval (adjacency T') (degreeMatrix T') (packedPoly N)))) := by sorry

end UniformADProbes.Trace
