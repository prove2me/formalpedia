-- Prove2me | Theorems.Thm_SpanForestStream_Unrestricted_eq_3_1
-- name    : SpanForestStream.Unrestricted.eq_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:30:54.289248+00:00
-- url     : https://prove2.me/theorems/dfefed14-c072-49f0-b90d-97b3d3ca2708
-- title:
--   §3.1, Eq. (3.1) — bilinear cut identity over F₂: Σ_{u∈C}(h_u y_uᵀ + y_u h_uᵀ) = H X_C Hᵀ
-- statement:
--   Let $G$ be a simple graph on $[v]$ with symmetric adjacency matrix $X$ over $\mathbb F_2$, $C\subseteq[v]$ a vertex set with diagonal indicator $I_C$, $H$ an $s\times v$ matrix over $\mathbb F_2$, $h_u=He_u$ its column $u$, and $y_u=HXe_u$ the retained syndrome of vertex $u$. Let $X_C$ be the **crossing-edge adjacency matrix**, with entry $1$ exactly at the pairs $(a,b)$ that are edges of $G$ with exactly one endpoint in $C$. Then $X_C=I_CX+XI_C$ over $\mathbb F_2$, and
--   $$M_C=\sum_{u\in C}\big(h_uy_u^{\mathsf T}+y_uh_u^{\mathsf T}\big)=H(I_CX+XI_C)H^{\mathsf T}=HX_CH^{\mathsf T}.\qquad(3.1)$$
--
--   The identity lets the algorithm assemble the syndrome of a cut from the stored vertex syndromes.
--
--   Differences from the source:
--   - generalization: H is the binary syndrome matrix of the sparse-recovery code of Lemma 3.1 → H is any s × v matrix over F₂; reason: the identity uses no property of H, and the syndrome matrix is an instance
--   - encoding: y_u = H x_u with x_u the adjacency column of u, and the identity y_u = HXe_u → y_u defined as (HX)e_u; reason: x_u = Xe_u, so the two definitions agree
--   - encoding: the crossing-edge adjacency matrix X_C → the 0/1 matrix with entry 1 iff G.Adj a b and exactly one of a, b lies in C; reason: the explicit meaning of 'crossing edge'
-- source:
--   Chao, Cen, Ma, Wang, Space-Optimal Algorithms for Spanning Forests in Dynamic Streams at Every Confidence Level, arXiv:2611.04365 (PDF sha256 00f5bb17…69c92), p. 13 (PDF 16), proof of Lemma 3.1, Eq. (3.1)

import Mathlib

namespace SpanForestStream.Unrestricted

/-- §3.1, Eq. (3.1): over `F₂`, with `X` the symmetric adjacency matrix of a simple graph `G` on
`[v]`, `I_C` the diagonal indicator of `C`, `h_u = H e_u` and `y_u = H X e_u`, the crossing-edge
adjacency matrix is `X_C = I_C X + X I_C`, and
`Σ_{u ∈ C} (h_u y_uᵀ + y_u h_uᵀ) = H (I_C X + X I_C) Hᵀ = H X_C Hᵀ`. -/
theorem eq_3_1 {v s : ℕ} (G : SimpleGraph (Fin v)) [DecidableRel G.Adj]
    (H : Matrix (Fin s) (Fin v) (ZMod 2)) (C : Finset (Fin v)) :
    let X : Matrix (Fin v) (Fin v) (ZMod 2) := G.adjMatrix (ZMod 2)
    let IC : Matrix (Fin v) (Fin v) (ZMod 2) := Matrix.diagonal fun u => if u ∈ C then 1 else 0
    let XC : Matrix (Fin v) (Fin v) (ZMod 2) :=
      fun a b => if G.Adj a b ∧ (a ∈ C ↔ b ∉ C) then 1 else 0
    let h : Fin v → Fin s → ZMod 2 := fun u => H.mulVec (Pi.single u 1)
    let y : Fin v → Fin s → ZMod 2 := fun u => (H * X).mulVec (Pi.single u 1)
    XC = IC * X + X * IC ∧
      ∑ u ∈ C, (Matrix.vecMulVec (h u) (y u) + Matrix.vecMulVec (y u) (h u)) =
        H * (IC * X + X * IC) * H.transpose ∧
      H * (IC * X + X * IC) * H.transpose = H * XC * H.transpose := by sorry

end SpanForestStream.Unrestricted
