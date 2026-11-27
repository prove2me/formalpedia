-- Prove2me | Theorems.Thm_TwoStageSRO_AsymOpt_Supplement_lemma_8
-- name    : TwoStageSRO.AsymOpt.Supplement.lemma_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T05:36:21.989081+00:00
-- url     : https://prove2.me/theorems/bf0d0d26-6c40-4d10-a97c-32985c53a75a
-- title:
--   Lemma 8, p. 39 — for a nonempty polyhedron T ⊆ Ξ, 1 ≤ θ^T_Ξ < ∞
-- statement:
--   Let $\Xi=\{\zeta\in\mathbb R^d : g_i^\top\zeta\ge g^0_i,\ i\in[\tilde m]\}$ with $\|g_i\|_*=1$ for every constraint, where $\|\cdot\|$ is an $\ell_p$-norm ($p\in[1,\infty]$) and $\|\cdot\|_*$ its dual norm. Let $\theta^T_\Xi$ be the reciprocal of the sine of the angle between a polyhedron $T$ and $\Xi$ (Definition 4). If $T\subseteq\Xi$ is a nonempty polyhedron, then
--   $$1\le\theta^T_\Xi<\infty.$$
--
--   Finiteness of $\theta^T_\Xi$ is what makes the radius of Theorem 3 a positive real number, and $\theta^T_\Xi\ge1$ is used in the induction step of its proof.
--
--   **Formalization Note** $\theta^T_\Xi$ takes values in `EReal`, so the finiteness is a genuine claim and not a junk value. The polyhedron $T$ is any set of the form $\{x : Ax\le b\}$.
--
--   Differences from the source:
--
--   - generalization: the appendices assume the representation of Ξ is minimal (p. 33) → minimality is not assumed; reason: θ^T_Ξ is defined from the faces of T and the hyperplanes H_i, and the finiteness argument (Hoffman's lemma for each face and hyperplane) never uses minimality; every Ξ with a minimal representation is covered
--   - encoding: max{1, −∞} for an empty inner maximum, infima over real θ ≥ 0 → values in EReal, the empty supremum is ⊥ and an infimum over no real θ is ⊤; reason: Lean convention reproducing the paper's values
-- source:
--   Bertsimas, Shtern, Sturt, Two-Stage Sample Robust Optimization, arXiv:1907.07142v4, p. 39, Lemma 8

import Mathlib
import Definitions.Def_CombOpt_MatchingPolytope_IsPolyhedron
import Definitions.Def_TwoStageSRO_AsymOpt_Geometry
import Definitions.Def_TwoStageSRO_AsymOpt_Supplement_PolyGeometry

open Matrix
open scoped ENNReal

namespace TwoStageSRO.AsymOpt.Supplement

/-- Bertsimas, Shtern, Sturt, Two-Stage Sample Robust Optimization, arXiv:1907.07142v4, p. 39, Lemma 8:
if `T ⊆ Ξ` is a nonempty polyhedron, then `1 ≤ θ^T_Ξ < ∞`.

**Formalization Note** `θ^T_Ξ` is `thetaPoly` (Definition 4, in `EReal`). The appendix's standing
normalization `‖gᵢ‖_* = 1` (p. 33) is the hypothesis `hG`; its other standing assumption, minimality of
the representation of `Ξ`, is not imposed (a disclosed strengthening). A polyhedron is a set
`{x : Ax ≤ b}` (published `CombOpt.MatchingPolytope.IsPolyhedron`). -/
theorem lemma_8 {n d r m mt : ℕ} (M : Model n d r m mt) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hG : ∀ k, dualNorm p (M.G k) = 1)
    (T : Set (Fin d → ℝ)) (hTpoly : CombOpt.MatchingPolytope.IsPolyhedron T)
    (hTXi : T ⊆ Xi M) (hTne : T.Nonempty) :
    1 ≤ thetaPoly M p T ∧ thetaPoly M p T < ⊤ := by sorry

end TwoStageSRO.AsymOpt.Supplement
