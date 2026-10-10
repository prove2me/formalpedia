-- Prove2me | Theorems.Thm_RunIntersect_Tight_mpri_subset_proj_mpri_gplus
-- name    : RunIntersect.Tight.mpri_subset_proj_mpri_gplus
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T15:35:44.657289+00:00
-- url     : https://prove2.me/theorems/291e327b-0060-4f72-8da0-f4c48e78134c
-- title:
--   §5.3.2, pp. 1035–1037 — projecting out z_p̄ from MP^RI_{G⁺} yields only inequalities valid for MP^RI_G
-- statement:
--   In the setting of §5.3 — $G=(V,E)$ kite-free β-acyclic with $\kappa\ge 2$ maximal edges, $\mathcal O$ a running intersection ordering of them, $\tilde e$ the last one, $\bar p=N(\tilde e)$ with $|\bar p|\ge 2$ and $\bar p\notin E$, and $G^+=(V,E\cup\{\bar p\})$ — every point of $\mathrm{MP}^{\mathrm{RI}}_G$ extends to a point of $\mathrm{MP}^{\mathrm{RI}}_{G^+}$:
--   $$\forall z\in\mathrm{MP}^{\mathrm{RI}}_G\ \ \exists t\in\mathbb R:\ (z \text{ with } z_{\bar p}:=t)\in\mathrm{MP}^{\mathrm{RI}}_{G^+}.$$
--
--   Equivalently, the projection of $\mathrm{MP}^{\mathrm{RI}}_{G^+}$ along $z_{\bar p}$ contains $\mathrm{MP}^{\mathrm{RI}}_G$: Fourier–Motzkin elimination of $z_{\bar p}$ only produces inequalities valid for $\mathrm{MP}^{\mathrm{RI}}_G$. With the two previous steps this gives $\mathrm{MP}^{\mathrm{RI}}_G\subseteq\mathrm{MP}_G$.
--
--   **Formalization Note** The statement is the conclusion of the elimination, in point form. No hypothesis on isolated nodes is needed: such nodes appear only in the rows $z_v\le 1$ on both sides.
-- source:
--   Del Pia and Khajavirad, The running intersection relaxation of the multilinear polytope, Math. Oper. Res. 46 (2021), pp. 1035–1037, §5.3.2 (proof of Theorem 3)

import Mathlib
import Definitions.Def_RunIntersect_Tight_Setting

namespace RunIntersect.Tight

theorem mpri_subset_proj_mpri_gplus {α : Type*} [Fintype α] [DecidableEq α]
    (G : Hypergraph α) (hkite : IsKiteFree G) (hβ : IsBetaAcyclic G)
    (O : List (Finset α)) (hOnd : O.Nodup) (hO : O.toFinset = maxEdges G) (hOri : IsRIOrder O)
    (hκ : 2 ≤ O.length)
    (hp : 2 ≤ (pbar O).card) (hpE : pbar O ∉ G.E) :
    ∀ z ∈ MPRI G, ∃ t : ℝ, Function.update z (Sum.inr (pbar O)) t ∈ MPRI (GplusLast G O) := by sorry

end RunIntersect.Tight
