-- Prove2me | Theorems.Thm_TreeCoverLB_lemma_4_8
-- name    : TreeCoverLB.lemma_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:25:13.896925+00:00
-- url     : https://prove2.me/theorems/c6ed1e75-c6e1-4c37-9643-c7fcd3b42581
-- title:
--   Lemma 4.8 (walk form, from its proof, p.16): a walk with nonzero winding between two vertices of a simplex has length $\ge c_0 r$
-- statement:
--   Let $p$ be prime, $G=\mathbb Z_p$, $D=d+1$, $\delta=\sqrt{2/D}$, $L=\sqrt{pD}$ and $c_0=\min\{\delta/4,1/L\}$. Let $M>0$, let $r\ge 4M/\delta$ be an integer, and let $\Gamma$ be a triangulation of the scaled cone $C_r$ over $E_dG$ with the base as a subcomplex, a simplicial $G$-action, and mesh at most $M$. If $u,v$ lie in one simplex of $\Gamma$, then every walk $Q$ in $\widetilde G_r$ from $u$ to $v$ with nonzero winding number satisfies
--   $$
--   \operatorname{len}(Q)\ \ge\ c_0\, r .
--   $$
--
--   Applied to the lifted tree path $\widetilde P_T(u,v)$ of (4.4), whose length is $d_T(\pi(u),\pi(v))$ and whose winding is $\ell_T(v)-\ell_T(u)$, this is Lemma 4.8: $d_T(\pi(u),\pi(v))\ge c_0r$ whenever $\ell_T(u)\neq\ell_T(v)$.
--
--   Differences from the source:
--   - generalization: d_T(π(u), π(v)) ≥ c₀r for a dominating tree T with ℓ_T(u) ≠ ℓ_T(v) → every walk in G̃_r from u to v with nonzero winding has length ≥ c₀r; reason: the proof establishes this bound and applies it to the lifted path P̃_T(u, v) of (4.4); every tree and every choice of lifts is an instance
--   - reading: constants c₀ = c₀(p, d) > 0 and r₀ = r₀(p, d) → c₀ = min{δ/4, 1/L} and r ≥ 4M/δ; reason: the proof's choice: 'Taking c₀ := min{δ/4, 1/L} and r₀ ≥ 4M/δ proves the claim'
--   - generalization: the triangulation Γ_r of Lemma 4.4 with its mesh constant M → any triangulation of C_r with properties 1–3 of Lemma 4.4 and any mesh bound M > 0; reason: the proof uses only these properties; Γ_r is one
-- source:
--   Chen, Huang, Tan, Xu, Improved Lower Bounds on Tree Covers, arXiv:2607.27264 (version of October 31, 2026), Lemma 4.8 and its proof, p.16 (PDF p.18), with Lemma 4.7, p.16

import Mathlib
import Definitions.Def_TreeCoverLB_EJoin
import Definitions.Def_TreeCoverLB_scaledCone
import Definitions.Def_TreeCoverLB_IsTriangulation
import Definitions.Def_TreeCoverLB_IsConeTriangulation
import Definitions.Def_TreeCoverLB_GWalk

open Classical

namespace TreeCoverLB

/-- **Lemma 4.8** (walk form, from its proof, p.16) (Chen, Huang, Tan, Xu, *Improved Lower Bounds on Tree Covers*, arXiv:2607.27264 (version of October 31, 2026), Lemma 4.8 and its proof, p.16 (PDF p.18),
with Lemma 4.7): let `p` be a prime, `G = ℤ_p`, `D = d + 1`, `δ = √(2/D)`, `L = √(pD)`
(Lemma 4.5) and `c₀ = min{δ/4, 1/L}`. Let `M > 0`, let `r ≥ 4M/δ` be an integer, and let `Γ` be a
triangulation of the cone `C_r` over `E_dG` with the base as a subcomplex, a simplicial `G`-action
and mesh at most `M`. If `u, v` lie in one simplex of `Γ`, then every walk in `G̃_r` from `u` to `v`
with nonzero winding number has weighted length at least `c₀ r`.

**Formalization Note** The paper's Lemma 4.8 bounds `d_T(π(u), π(v)) ≥ c₀ r` when the winding labels
of a tree `T` differ, `ℓ_T(u) ≠ ℓ_T(v)`. Its proof shows exactly this walk statement and applies
it to the lifted tree path `P̃_T(u, v)` of (4.4), which has length `d_T(π(u), π(v))` and winding
`ℓ_T(v) − ℓ_T(u)`; "Taking c₀ := min{δ/4, 1/L} and r₀ ≥ 4M/δ proves the claim." Quantifying over all
walks covers every tree and every choice of the lifts of §4.2. `Γ` is any triangulation with
properties 1–3 of Lemma 4.4, not only the one constructed there. -/
theorem lemma_4_8 (p : ℕ) [Fact p.Prime] (d : ℕ) (M : ℝ) (hM : 0 < M) (r : ℕ)
    (hr : 4 * M / Real.sqrt (2 / ((d : ℝ) + 1)) ≤ r)
    (Γ : Finset (Finset (Fin (d + 1) × ZMod p → ℝ))) (hΓ : IsConeTriangulation p d r Γ)
    (hmesh : MeshLE Γ M) (σ : Finset (Fin (d + 1) × ZMod p → ℝ)) (hσ : σ ∈ Γ)
    (u v : Fin (d + 1) × ZMod p → ℝ) (hu : u ∈ σ) (hv : v ∈ σ) (w : GWalk r Γ u v)
    (hw : w.winding ≠ 0) :
    min (Real.sqrt (2 / ((d : ℝ) + 1)) / 4) (1 / Real.sqrt ((p : ℝ) * ((d : ℝ) + 1))) * r ≤ w.length := by sorry

end TreeCoverLB
