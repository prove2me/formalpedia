-- Prove2me | Theorems.Thm_RankOneBTF_proposition_2
-- name    : RankOneBTF.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:24:03.854893+00:00
-- url     : https://prove2.me/theorems/a53a9b86-f406-4246-88f3-76d282cc3bce
-- title:
--   Proposition 2 — LP-type problems with $0\le w\le1$ are robust to monotone adversaries
-- statement:
--   Let $R$ be a fixed feasible region of points $v$ of a decision space, with tensor part $\mathcal W(v)$ satisfying $0\le w_{ijk}(v)\le1$ for all $v\in R$ and all $(i,j,k)$. Let the ground truth point $\bar v$ have tensor part $\bar{\mathcal W}=\bar x\otimes\bar y\otimes\bar z$. For an input tensor $\mathcal G$, Problem (Rec) minimizes the objective of (extP),
--   $$
--   \sum_{(i,j,k)\in S_0(\mathcal G)}w_{ijk}(v)+\sum_{(i,j,k)\in S_1(\mathcal G)}\bigl(1-w_{ijk}(v)\bigr),
--   $$
--   over $R$. If $\bar v$ is the unique optimal solution for the input $\mathcal G$, and $\mathcal G'$ is obtained from $\mathcal G$ by an arbitrary sequence of monotone transformations (each entry of $\mathcal G'$ equals the entry of $\mathcal G$ or of $\bar{\mathcal W}$), then $\bar v$ is also the unique optimal solution for the input $\mathcal G'$. That is, Problem (Rec) is **robust**.
--
--   Robustness is what transfers recovery guarantees from the fully-random to the semi-random corruption model.
--
--   **Formalization Note** The decision space is an arbitrary type `V` with a map `Wof` to the tensor part; for the paper's variables $(x,y,z,\mathcal W)$ take the projection and $\bar v=(\bar x,\bar y,\bar z,\bar{\mathcal W})$.
--
--   Differences from the source:
--   - generalization: optimization variables (x, y, z, W), possibly with additional variables (proof, p.6) → an arbitrary decision space V with a tensor-part map Wof and a ground truth point v̄ whose tensor part is W̄; reason: the objective depends only on W; V = ℝⁿ×ℝᵐ×ℝˡ×ℝ^{n×m×l} with the projection and v̄ = (x̄, ȳ, z̄, W̄) is the printed case
--   - reading: "whose feasible region satisfies 0 ≤ w_ijk ≤ 1" → a fixed set R, independent of the input tensor, on which 0 ≤ w_ijk ≤ 1; reason: the proof (p.6) evaluates the optimum for G′ inside the problem for G, which needs the same region for both
--   - encoding: G′ obtained from G by an arbitrary sequence of monotone transformations → every entry of G′ equals the entry of G or of W̄; reason: a sequence of reversions changes exactly a subset of the entries where G differs from W̄; same instances
-- source:
--   Del Pia, Khajavirad, Rank-one Boolean tensor factorization and the multilinear polytope, arXiv:2202.07053v3, §2.2, Proposition 2, p.5 (definition of robust, p.5; proof p.6)

import Mathlib
import Definitions.Def_RankOneBTF_lpObjective

namespace RankOneBTF

/-- **Proposition 2** (arXiv:2202.07053v3, §2.2, p.5): "Denote by Problem (Rec) a minimization
problem whose objective function is identical to that of Problem (extP) and whose feasible
region satisfies 0 ≤ w_ijk ≤ 1 for all i ∈ [n], j ∈ [m], k ∈ [l]. Then Problem (Rec) is
robust." An optimization problem is *robust* "if whenever it recovers the ground truth for an
input tensor G, then it also recovers the ground truth if an adversary modifies G by applying
an arbitrary sequence of monotone transformations" (p.5).

**Formalization Note** The decision space is any type `V` (the paper's proof: "the proof
follows from the same line of arguments, if Problem (Rec) contains additional variables");
`Wof v` is the tensor part `W` of a point `v`, and the objective is that of (extP),
`Σ_{S₀} w_ijk + Σ_{S₁}(1 − w_ijk)` for the input tensor (`objW`). The feasible region `R` is a
fixed set that does not depend on the input tensor (the proof evaluates the optimum of the
problem for `G'` in the problem for `G`). The ground truth is a point `v̄ ∈ V` whose tensor part
is `W̄ = x̄ ⊗ ȳ ⊗ z̄`; with `V = ℝⁿ × ℝᵐ × ℝˡ × ℝ^{n×m×l}` it is `(x̄, ȳ, z̄, W̄)`. A sequence of
monotone transformations produces a tensor `G'` that agrees, entry by entry, with `G` or with
`W̄`. -/
theorem proposition_2 {n m l : ℕ} {V : Type*} (R : Set V)
    (Wof : V → Fin n → Fin m → Fin l → ℝ)
    (hbox : ∀ v ∈ R, ∀ i j k, 0 ≤ Wof v i j k ∧ Wof v i j k ≤ 1)
    (xb : Fin n → Bool) (yb : Fin m → Bool) (zb : Fin l → Bool) (vbar : V)
    (hvbar : Wof vbar = realTensor (groundTruth xb yb zb))
    (G G' : BTensor n m l)
    (hmod : ∀ i j k, G' i j k = G i j k ∨ G' i j k = groundTruth xb yb zb i j k)
    (hrec : IsUniqueOptimalOn R (fun v => objW G (Wof v)) vbar) :
    IsUniqueOptimalOn R (fun v => objW G' (Wof v)) vbar := by sorry

end RankOneBTF
