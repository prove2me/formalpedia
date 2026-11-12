-- Prove2me | Theorems.Thm_OuterplanarL1Tan_Linear_exists_outerFacialWalk_of_connected
-- name    : OuterplanarL1Tan.Linear.exists_outerFacialWalk_of_connected
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T20:50:28.658748+00:00
-- url     : https://prove2.me/theorems/89d20e8a-a029-4d25-8757-2bd1a7de73ad
-- title:
--   Every connected plane drawing has an outer facial walk with an exterior collar
-- statement:
--   Let $G$ be a connected simple graph on a finite vertex type $V$, and let $D$ be a plane drawing of $G$ (`PlaneDrawing G`: injective vertex points, each edge an injective arc, an arc meets a vertex point only at its own ends, and two distinct edges' arcs meet only at common endpoints). Then $D$ has an outer facial walk (`OuterFacialWalk D`): a cyclic sequence $u_0, \dots, u_{n-1}$ of vertices, $n > 0$, together with a collar $c : \mathbb R \times \mathbb R \to \mathbb R^2$ such that:
--
--   - the set $\{u_j\}$ is exactly the set of vertices whose point lies in the closure of the outer face (the unbounded complementary region of the drawing);
--   - each step $u_j \to u_{j+1 \bmod n}$ is an edge, unless $V$ is a single vertex;
--   - no directed step is used twice;
--   - the level-$0$ curve $c(0, \cdot)$ runs, on $[j/n, (j+1)/n]$, along the arc of the edge $u_j u_{j+1}$ at the arc's own parameter, and its image is the frontier of the outer face;
--   - for $r \in (0, 1]$ the curves $c(r, \cdot)$ are simple closed curves in the outer face, pairwise disjoint and each enclosing the whole drawing, with $c$ continuous on $[0,1]^2$.
--
--   So the collar fixes the walk as the actual boundary traversal of the outer face.
--
--   Tan's paper uses this without proof. Section 2.1 (printed p. 2) says "let $b_1, \dots, b_m$ be the vertices lying on the outer face in this order", and the proof of Theorem 1 (§3.3, printed p. 7) applies the pattern map, and with it Lemmas 2 and 5, to every connected component of every residual graph in its inherited drawing. So `OuterplanarL1Tan.Linear.theorem_1` reduces to this statement together with the mission's lemmas.
--
--   Connectedness is needed: a drawing of two isolated vertices has no closed walk through both boundary vertices. For a single vertex, $n = 1$ and the collar circles shrink to the point.
-- source:
--   Zihan Tan, Improved Embedding of k-Outerplanar Metrics into ℓ1, ACM STOC 2027 submission 262, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/262.pdf, p. 2, §2.1 (PDF p. 3), "let b₁, …, bₘ be the vertices lying on the outer face in this order", applied to each residual component in §3.3 (printed p. 7)

import Definitions.Def_OuterplanarL1Tan_Linear_PlaneGeometry

open OuterplanarL1Tan.Linear in
theorem OuterplanarL1Tan.Linear.exists_outerFacialWalk_of_connected {V : Type} [Fintype V]
    {G : SimpleGraph V} (connected : G.Connected) (D : PlaneDrawing G) :
    Nonempty (OuterFacialWalk D) := by sorry
