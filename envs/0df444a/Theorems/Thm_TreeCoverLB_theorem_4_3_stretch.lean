-- Prove2me | Theorems.Thm_TreeCoverLB_theorem_4_3_stretch
-- name    : TreeCoverLB.theorem_4_3_stretch
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:26:36.471381+00:00
-- url     : https://prove2.me/theorems/f346512c-50b0-431b-8c92-4bb852a0d9f4
-- title:
--   Proof of Theorem 4.3: $d_r$ is a metric and every $k$-tree cover of $X_r$ has stretch $\ge (c_0/M)\,r$
-- statement:
--   Let $p$ be prime, $k\ge 2$, $G=\mathbb Z_p$, and suppose there is a continuous $G$-equivariant map $|I_{p,k}|\to|E_dG|$. Let $D=d+1$, $\delta=\sqrt{2/D}$, $L=\sqrt{pD}$, $c_0=\min\{\delta/4,1/L\}$, $M>0$, let $r\ge 4M/\delta$ be an integer, and let $\Gamma$ be a triangulation of the scaled cone $C_r$ over $E_dG$ with the base as a subcomplex, a simplicial $G$-action, and mesh at most $M$. Let $(X_r,d_r)$ be the hard metric built from $\Gamma$. Then
--
--   1. $d_r$ is a metric on $X_r$;
--   2. every size-$k$ tree cover of $(X_r,d_r)$ has distortion at least
--   $$
--   \beta_r=\frac{c_0}{M}\,r .
--   $$
--
--   Differences from the source:
--   - generalization: the triangulation Γ_r of Lemma 4.4 with mesh constant M → any triangulation of C_r with properties 1–3 of Lemma 4.4 and any mesh bound M > 0; reason: the argument uses only these properties; Γ_r is one
--   - reading: for sufficiently large r → r ≥ 4M/δ; reason: the threshold r₀ of Lemma 4.8's proof, which also gives r > M/δ (π injective on simplices, p.13)
--   - encoding: X_r := V(G_r) after contracting vertices at zero distance; d_r the shortest-path metric of G_r → the quotient of V(Γ) by 'boundary vertices in one orbit'; d_r = infimum of G̃_r-walk lengths between fixed representatives; reason: zero-distance pairs are exactly the boundary orbits; walk lengths do not depend on representatives
-- source:
--   Chen, Huang, Tan, Xu, Improved Lower Bounds on Tree Covers, arXiv:2607.27264 (version of October 31, 2026), proof of Theorem 4.3, p.17 (PDF p.19); 'd_r is a metric', p.13 (PDF p.15)

import Mathlib
import Definitions.Def_TreeCoverLB_IsFinMetric
import Definitions.Def_TreeCoverLB_WeightedTree
import Definitions.Def_TreeCoverLB_IsTreeCover
import Definitions.Def_TreeCoverLB_realization
import Definitions.Def_TreeCoverLB_EJoin
import Definitions.Def_TreeCoverLB_agreementComplex
import Definitions.Def_TreeCoverLB_IsAgreementIndexMap
import Definitions.Def_TreeCoverLB_scaledCone
import Definitions.Def_TreeCoverLB_IsTriangulation
import Definitions.Def_TreeCoverLB_IsConeTriangulation
import Definitions.Def_TreeCoverLB_GWalk
import Definitions.Def_TreeCoverLB_hardMetric

open Classical

namespace TreeCoverLB

/-- **Proof of Theorem 4.3 — every `k`-tree cover of `X_r` has stretch at least `β_r = (c₀/M) r`**
(Chen, Huang, Tan, Xu, *Improved Lower Bounds on Tree Covers*, arXiv:2607.27264 (version of October 31, 2026), proof of Theorem 4.3, p.17 (PDF p.19); the hard metric of §4.1, p.13): let `p` be a prime,
`k ≥ 2`, `G = ℤ_p`, `ψ : |I_{p,k}| → |E_dG|` continuous and `G`-equivariant, `D = d + 1`,
`δ = √(2/D)`, `L = √(pD)`, `c₀ = min{δ/4, 1/L}`. Let `M > 0`, let `r ≥ 4M/δ` be an integer, and let
`Γ` be a triangulation of the cone `C_r` over `E_dG` with the base as a subcomplex, a simplicial
`G`-action and mesh at most `M`. Let `X_r` be the vertex set of `Γ` with each boundary `G`-orbit
contracted to a point and `d_r` the shortest-path distance of `G̃_r`. Then `d_r` is a metric on `X_r`,
and every size-`k` tree cover of `(X_r, d_r)` has distortion at least `(c₀/M) r`.

**Formalization Note** "`d_r` is a metric" is the paper's "After the zero-weight components have been
contracted, the shortest-path distance d_r on G_r is a metric" (p.13). `Γ` is any triangulation with
properties 1–3 of Lemma 4.4 (the paper fixes the one Lemma 4.4 provides), and the paper's
"sufficiently large r" is the explicit `r ≥ 4M/δ` of Lemma 4.8. -/
theorem theorem_4_3_stretch (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 2 ≤ k) (d : ℕ)
    (ψ : ((Fin k → ZMod p) → ℝ) → (Fin (d + 1) × ZMod p → ℝ))
    (hψ : IsAgreementIndexMap p k d ψ) (M : ℝ) (hM : 0 < M) (r : ℕ)
    (hr : 4 * M / Real.sqrt (2 / ((d : ℝ) + 1)) ≤ r)
    (Γ : Finset (Finset (Fin (d + 1) × ZMod p → ℝ))) (hΓ : IsConeTriangulation p d r Γ)
    (hmesh : MeshLE Γ M) :
    IsFinMetric (hardDist r Γ) ∧
      ∀ (T : Fin k → WeightedTree (HardSpace r Γ)) (α : ℝ), IsTreeCover (hardDist r Γ) T α →
        min (Real.sqrt (2 / ((d : ℝ) + 1)) / 4) (1 / Real.sqrt ((p : ℝ) * ((d : ℝ) + 1))) / M * r ≤ α := by sorry

end TreeCoverLB
