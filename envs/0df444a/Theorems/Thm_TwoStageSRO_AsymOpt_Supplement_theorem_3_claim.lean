-- Prove2me | Theorems.Thm_TwoStageSRO_AsymOpt_Supplement_theorem_3_claim
-- name    : TwoStageSRO.AsymOpt.Supplement.theorem_3_claim
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T05:36:56.570798+00:00
-- url     : https://prove2.me/theorems/e025706a-13ff-423e-9fc1-72a1b59062ed
-- title:
--   Claim in the proof of Theorem 3, p. 49 — on a face F of T of dimension k, radius α_kϵ works with ζ̄ ∈ F
-- statement:
--   Let $\Xi=\{\zeta\in\mathbb R^d : g_i^\top\zeta\ge g^0_i,\ i\in[\tilde m]\}$ with $\|g_i\|_*=1$ for every constraint ($\ell_p$-norm $\|\cdot\|$, $p\in[1,\infty]$, dual norm $\|\cdot\|_*$), and write $B(\hat\zeta,\epsilon)=\{\zeta:\|\zeta-\hat\zeta\|\le\epsilon\}$. Let $T\subseteq\Xi$ be a nonempty polyhedron, $\bar\epsilon>0$ and $\lambda\in(0,1)$, and let
--   $$\epsilon=\Big(\frac{\lambda}{2\theta^T_\Xi}\Big)^{\dim(T)-\underline{\dim}(T)}\lambda\min\{\bar\epsilon,\Delta_\Xi(T)\}$$
--   be the radius of Theorem 3, where $\theta^T_\Xi$ is Definition 4, $\Delta_\Xi(T)$ is Definition 3, and $\underline{\dim}(T)$ is the dimension of the minimal faces of $T$. For each dimension $k\in\{\underline{\dim}(T),\dots,\dim(T)\}$ define
--   $$\alpha_k=\Big(\frac{2\theta^T_\Xi}{\lambda}\Big)^{\dim(T)-k}.$$
--   Then for each $F\in\mathrm{Faces}(T)$ with $\dim(F)=k$ and each $\hat\zeta\in F$ there exists $\bar\zeta\in F$ such that
--   $$B(\hat\zeta,\alpha_k\epsilon)\cap\Xi\subseteq\{\lambda\zeta+(1-\lambda)\bar\zeta : \zeta\in B(\bar\zeta,\bar\epsilon)\cap\Xi\}.\qquad(54)$$
--
--   The paper proves this by induction on $k$, and Theorem 3 is its case $F=T$, $k=\dim(T)$, $\alpha_{\dim(T)}=1$.
--
--   **Formalization Note** $\epsilon$ and $\alpha_k$ are the defined quantities of the mission's polyhedral-geometry definition, with $\theta^T_\Xi$ converted to a real number (exact, since it is finite by Lemma 8). No finiteness of $\theta^T_\Xi$ or $\Delta_\Xi(T)$ is assumed.
--
--   Differences from the source:
--
--   - generalization: the appendices assume the representation of Ξ is minimal (p. 33) → minimality is not assumed; reason: the proof uses only that F ∩ H_i is a face of F (true because g_iᵀζ ≥ g⁰_i is valid on F ⊆ Ξ) and Lemma 5, which holds without minimality; every Ξ with a minimal representation is covered
--   - encoding: θ^T_Ξ and ∆_Ξ(T) as extended reals inside real radii → θ^T_Ξ enters through EReal.toReal and min{ϵ̄, ∆_Ξ(T)} is taken in EReal; reason: θ^T_Ξ is finite (Lemma 8) and min{ϵ̄, ∆_Ξ(T)} ∈ [0, ϵ̄], so both conversions are exact
-- source:
--   Bertsimas, Shtern, Sturt, Two-Stage Sample Robust Optimization, arXiv:1907.07142v4, p. 49, Claim in the proof of Theorem 3, (54)

import Mathlib
import Definitions.Def_CombOpt_MatchingPolytope_IsPolyhedron
import Definitions.Def_TwoStageSRO_AsymOpt_Geometry
import Definitions.Def_TwoStageSRO_AsymOpt_Supplement_PolyGeometry

open Matrix
open scoped ENNReal

namespace TwoStageSRO.AsymOpt.Supplement

/-- Bertsimas, Shtern, Sturt, Two-Stage Sample Robust Optimization, arXiv:1907.07142v4, p. 49, Claim in the
proof of Theorem 3: let `T ⊆ Ξ` be a nonempty polyhedron, `ϵ̄ > 0`, `λ ∈ (0, 1)`, and let `ϵ` be the
radius of Theorem 3. For each `k ∈ {dim̲(T), …, dim(T)}` put `α_k = (2θ^T_Ξ / λ)^{dim(T) − k}`. Then for
each `F ∈ Faces(T)` with `dim(F) = k` and each `ζ̂ ∈ F` there is `ζ̄ ∈ F` with
`B(ζ̂, α_k ϵ) ∩ Ξ ⊆ {λζ + (1 − λ)ζ̄ : ζ ∈ B(ζ̄, ϵ̄) ∩ Ξ}` (54).

**Formalization Note** `ϵ` is `epsThm3 M p T εbar lam` and `α_k` is `alphaClaim M p T lam k`, so the
setting (`T`, `ϵ̄`, `λ`) is that of Theorem 3 (p. 48). The standing normalization `‖gᵢ‖_* = 1` (p. 33) is
`hG`; minimality of the representation of `Ξ` is not imposed (a disclosed strengthening). -/
theorem theorem_3_claim {n d r m mt : ℕ} (M : Model n d r m mt) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hG : ∀ k, dualNorm p (M.G k) = 1)
    (T : Set (Fin d → ℝ)) (hTpoly : CombOpt.MatchingPolytope.IsPolyhedron T)
    (hTXi : T ⊆ Xi M) (hTne : T.Nonempty)
    (εbar : ℝ) (hεbar : 0 < εbar) (lam : ℝ) (hlam : lam ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ k : ℕ, minFaceDim T ≤ k → k ≤ polyDim T →
      ∀ F, IsFaceOf T F → polyDim F = k →
        ∀ zhat ∈ F, ∃ zbar ∈ F,
          ball p zhat (alphaClaim M p T lam k * epsThm3 M p T εbar lam) ∩ Xi M ⊆
            (fun ζ => lam • ζ + (1 - lam) • zbar) '' (ball p zbar εbar ∩ Xi M) := by sorry

end TwoStageSRO.AsymOpt.Supplement
