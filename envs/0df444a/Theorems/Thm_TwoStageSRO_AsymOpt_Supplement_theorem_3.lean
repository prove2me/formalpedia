-- Prove2me | Theorems.Thm_TwoStageSRO_AsymOpt_Supplement_theorem_3
-- name    : TwoStageSRO.AsymOpt.Supplement.theorem_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T05:38:03.957002+00:00
-- url     : https://prove2.me/theorems/411c73dd-137c-4b45-a490-298517ccb4d8
-- title:
--   Theorem 3, p. 48 — explicit uniform radius ϵ = (λ/2θ^T_Ξ)^{dim T − dim̲ T} λ min{ϵ̄, ∆_Ξ(T)} for λ-shrunk balls on a polyhedron T ⊆ Ξ
-- statement:
--   Let $\Xi=\{\zeta\in\mathbb R^d : g_i^\top\zeta\ge g^0_i,\ i\in[\tilde m]\}$ with $\|g_i\|_*=1$ for every constraint ($\ell_p$-norm $\|\cdot\|$, $p\in[1,\infty]$, dual norm $\|\cdot\|_*$), and write $B(\hat\zeta,\epsilon)=\{\zeta:\|\zeta-\hat\zeta\|\le\epsilon\}$. Let $T\subseteq\Xi$ be a nonempty polyhedron. Given $\bar\epsilon>0$ and $\lambda\in(0,1)$, define
--   $$\epsilon=\Big(\frac{\lambda}{2\theta^T_\Xi}\Big)^{\dim(T)-\underline{\dim}(T)}\lambda\min\{\bar\epsilon,\Delta_\Xi(T)\},$$
--   where $\theta^T_\Xi$ is the reciprocal sine of the angle between $T$ and $\Xi$ (Definition 4), $\Delta_\Xi(T)$ is the radius of $T$ with respect to $\Xi$ (Definition 3), and $\underline{\dim}(T)$ is the dimension of the minimal faces of $T$. Then for every $\hat\zeta\in T$ there exists $\bar\zeta\in T$ such that
--   $$B(\hat\zeta,\epsilon)\cap\Xi\subseteq\{\lambda\zeta+(1-\lambda)\bar\zeta : \zeta\in B(\bar\zeta,\bar\epsilon)\cap\Xi\}.$$
--
--   The radius $\epsilon$ does not depend on $\hat\zeta$. With $T=\Xi^*$ this is the inclusion used in the proof of Lemma 2 (display (3)), here with an explicit radius in terms of the geometry of $T$ and $\Xi$.
--
--   **Formalization Note** $\epsilon$ is the defined quantity of the mission's polyhedral-geometry definition. No finiteness of $\theta^T_\Xi$ or $\Delta_\Xi(T)$ is assumed; $\theta^T_\Xi$ is converted to a real number, which is exact because it is finite (Lemma 8).
--
--   Differences from the source:
--
--   - generalization: the appendices assume the representation of Ξ is minimal (p. 33) → minimality is not assumed; reason: the proof (via the Claim and Lemma 5) never uses minimality, and redundant constraints only add hyperplanes to ρ₁ and to θ^T_Ξ; every Ξ with a minimal representation is covered
--   - encoding: θ^T_Ξ and ∆_Ξ(T) as extended reals inside a real radius → θ^T_Ξ enters through EReal.toReal and min{ϵ̄, ∆_Ξ(T)} is taken in EReal; reason: θ^T_Ξ is finite (Lemma 8) and min{ϵ̄, ∆_Ξ(T)} ∈ [0, ϵ̄], so both conversions are exact
-- source:
--   Bertsimas, Shtern, Sturt, Two-Stage Sample Robust Optimization, arXiv:1907.07142v4, p. 48, Theorem 3

import Mathlib
import Definitions.Def_CombOpt_MatchingPolytope_IsPolyhedron
import Definitions.Def_TwoStageSRO_AsymOpt_Geometry
import Definitions.Def_TwoStageSRO_AsymOpt_Supplement_PolyGeometry

open Matrix
open scoped ENNReal

namespace TwoStageSRO.AsymOpt.Supplement

/-- Bertsimas, Shtern, Sturt, Two-Stage Sample Robust Optimization, arXiv:1907.07142v4, p. 48, Theorem 3:
let `T ⊆ Ξ` be a nonempty polyhedron. Given `ϵ̄ > 0` and `λ ∈ (0, 1)`, define
`ϵ = (λ / (2θ^T_Ξ))^{dim(T) − dim̲(T)} λ min{ϵ̄, ∆_Ξ(T)}`. Then for all `ζ̂ ∈ T` there is `ζ̄ ∈ T` with
`B(ζ̂, ϵ) ∩ Ξ ⊆ {λζ + (1 − λ)ζ̄ : ζ ∈ B(ζ̄, ϵ̄) ∩ Ξ}`.

**Formalization Note** `ϵ` is `epsThm3 M p T εbar lam`, built from `θ^T_Ξ` (`thetaPoly`, Definition 4),
`∆_Ξ(T)` (`polyRadius`, Definition 3), `dim` and `dim̲`. The standing normalization `‖gᵢ‖_* = 1`
(p. 33) is `hG`; minimality of the representation of `Ξ` is not imposed (a disclosed strengthening). -/
theorem theorem_3 {n d r m mt : ℕ} (M : Model n d r m mt) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hG : ∀ k, dualNorm p (M.G k) = 1)
    (T : Set (Fin d → ℝ)) (hTpoly : CombOpt.MatchingPolytope.IsPolyhedron T)
    (hTXi : T ⊆ Xi M) (hTne : T.Nonempty)
    (εbar : ℝ) (hεbar : 0 < εbar) (lam : ℝ) (hlam : lam ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ zhat ∈ T, ∃ zbar ∈ T,
      ball p zhat (epsThm3 M p T εbar lam) ∩ Xi M ⊆
        (fun ζ => lam • ζ + (1 - lam) • zbar) '' (ball p zbar εbar ∩ Xi M) := by sorry

end TwoStageSRO.AsymOpt.Supplement
