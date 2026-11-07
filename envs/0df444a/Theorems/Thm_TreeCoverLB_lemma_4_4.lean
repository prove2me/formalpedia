-- Prove2me | Theorems.Thm_TreeCoverLB_lemma_4_4
-- name    : TreeCoverLB.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:24:43.027186+00:00
-- url     : https://prove2.me/theorems/ce2c528f-acca-4cc0-a6fc-ad2603265b33
-- title:
--   Lemma 4.4: an equivariant triangulation $\Gamma_r$ of $C_r$ with bounded mesh and $\Theta(r^D)$ vertices
-- statement:
--   Let $p$ be prime, $G=\mathbb Z_p$, $K=E_dG$ and $D=d+1$. There are constants $M,c_1,c_2,c_3>0$ depending only on $p,d$ such that for every integer $r\ge 1$ the scaled cone $C_r=rC(K)$ has a finite triangulation $\Gamma_r$ with
--
--   1. the base $r|K|$ a subcomplex of $\Gamma_r$;
--   2. the $G$-action on $\Gamma_r$ simplicial;
--   3. every simplex of Euclidean diameter at most $M$;
--   4. $c_1r^D\le|V(\Gamma_r)|\le c_2r^D$ and $|V(\Gamma_r)\cap r|K||\le c_3r^{D-1}$.
--
--   The vertices of $\Gamma_r$ are the points of the hard metric before the boundary identifications.
--
--   Differences from the source:
--   - encoding: a triangulation as a collection of simplices with the 'empty or a common face' condition → a finset of affinely independent vertex sets with conv σ₁ ∩ conv σ₂ = conv (σ₁ ∩ σ₂); reason: equivalent for affinely independent vertex sets
--   - encoding: Θ_K(r^D), O_K(r^{D−1}) and a constant M = M(K) → explicit constants M, c₁, c₂, c₃ > 0 chosen before r, depending only on p and d; reason: the meaning of the subscripted asymptotic notation (p.8)
--   - encoding: Euclidean diameter of a simplex → largest distance between two of its vertices; reason: equal for a convex hull
-- source:
--   Chen, Huang, Tan, Xu, Improved Lower Bounds on Tree Covers, arXiv:2607.27264 (version of October 31, 2026), Lemma 4.4, p.12 (PDF p.14); proof in Appendix B, pp.35–38

import Mathlib
import Definitions.Def_TreeCoverLB_EJoin
import Definitions.Def_TreeCoverLB_scaledCone
import Definitions.Def_TreeCoverLB_IsTriangulation
import Definitions.Def_TreeCoverLB_IsConeTriangulation

open Classical

namespace TreeCoverLB

/-- **Lemma 4.4** (Chen, Huang, Tan, Xu, *Improved Lower Bounds on Tree Covers*, arXiv:2607.27264 (version of October 31, 2026), Lemma 4.4, p.12 (PDF p.14); proof in Appendix B, pp.35–38): let `p` be a
prime, `G = ℤ_p`, `K = E_dG` and `D = d + 1`. For every integer `r ≥ 1`, the scaled cone
`C_r = r C(K)` has a finite triangulation `Γ_r` such that
1. the base `r|K|` of `C_r` is a subcomplex of `Γ_r`;
2. the `G`-action on `Γ_r` is simplicial;
3. every simplex has Euclidean diameter at most a constant `M = M(K)` independent of `r`;
4. `|V(Γ_r)| = Θ_K(r^D)` and `|V(Γ_r) ∩ r|K|| = O_K(r^{D−1})`.

**Formalization Note** The constants `M, c₁, c₂, c₃` are chosen before `r` and depend only on `p`
and `d` (i.e. on `K`). Clauses 1–2 together with "`Γ` triangulates `C_r`" are `IsConeTriangulation`;
clause 3 is `MeshLE`; clause 4 is `c₁ r^D ≤ |V(Γ)| ≤ c₂ r^D` and `|V(Γ) ∩ r|K|| ≤ c₃ r^{D−1}`. -/
theorem lemma_4_4 (p : ℕ) [Fact p.Prime] (d : ℕ) :
    ∃ M : ℝ, 0 < M ∧ ∃ c₁ c₂ c₃ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ 0 < c₃ ∧
      ∀ r : ℕ, 1 ≤ r → ∃ Γ : Finset (Finset (Fin (d + 1) × ZMod p → ℝ)),
        IsConeTriangulation p d r Γ ∧ MeshLE Γ M ∧
        c₁ * (r : ℝ) ^ (d + 1) ≤ ((vertexSet Γ).card : ℝ) ∧
        ((vertexSet Γ).card : ℝ) ≤ c₂ * (r : ℝ) ^ (d + 1) ∧
        (((vertexSet Γ).filter (· ∈ coneBase (EJoin d (ZMod p)) r)).card : ℝ) ≤
          c₃ * (r : ℝ) ^ d := by sorry

end TreeCoverLB
