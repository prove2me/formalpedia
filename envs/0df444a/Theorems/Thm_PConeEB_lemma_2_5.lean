-- Prove2me | Theorems.Thm_PConeEB_lemma_2_5
-- name    : PConeEB.lemma_2_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:32:09.814161+00:00
-- url     : https://prove2.me/theorems/dacbdf09-267e-49bc-9ed3-f77a4a7bb781
-- title:
--   Lemma 2.5 — projections onto $\{z\}^\perp$ and onto a ray
-- statement:
--   Let $K$ be a pointed closed convex cone and $z\in\partial K^*\setminus\{0\}$ such that $\mathcal F:=\{z\}^\perp\cap K$ is a one-dimensional proper face, say $\mathcal F=\{tf:t\ge0\}$ with $f\in K\setminus\{0\}$. Let $\eta>0$, $v\in\partial K\cap B(\eta)\setminus\mathcal F$, $w=P_{\{z\}^\perp}v$ and $u=P_{\mathcal F}w$ with $u\ne w$. Then $\langle f,z\rangle=0$, and
--   $$
--   \|v-w\|=\frac{|\langle z,v\rangle|}{\|z\|},\qquad\|u-w\|=\begin{cases}\left\|v-\frac{\langle z,v\rangle}{\|z\|^2}z-\frac{\langle f,v\rangle}{\|f\|^2}f\right\|&\text{if }\langle f,v\rangle\ge0,\\[1ex]\left\|v-\frac{\langle z,v\rangle}{\|z\|^2}z\right\|&\text{otherwise.}\end{cases}
--   $$
--   Moreover $\langle f,v\rangle\ge0$ if and only if $\langle f,w\rangle\ge0$, and in that case $u=P_{\operatorname{span}\mathcal F}w$. If $\langle f,v\rangle<0$, then $u=0$.
--
--   The lemma turns the infimum (2.13) into an explicit quantity when the face is an extreme ray.
--
--   Differences from the source:
--   - encoding: a one-dimensional proper face F with F = {tf | t ≥ 0}, f ∈ K \ {0} → K ∩ {z}^⊥ ≠ K, f ∈ K, f ≠ 0 and K ∩ {z}^⊥ = {t • f | 0 ≤ t}; reason: the ray is one-dimensional by f ≠ 0; the same instances
--   - encoding: ∂K, ∂K* → frontier K, frontier of ProperCone.innerDual K; reason: the proof of the lemma uses neither boundary, so the convention does not matter
--   - encoding: a finite dimensional Euclidean space E → a type E with InnerProductSpace ℝ E, FiniteDimensional ℝ E and CompleteSpace E; reason: Mathlib conventions; CompleteSpace is required by ProperCone.innerDual and holds in every finite dimensional space
-- source:
--   Lindstrom, Lourenço & Pong, Optimal error bounds in the absence of constraint qualifications, arXiv:2109.11729v4, Lemma 2.5, p.9

import Mathlib
import Definitions.Def_MoreauProx_Decomposition_Cones
import Definitions.Def_PConeEB_hyperplane

open MoreauProx.Decomposition (IsClosedConvexCone IsProj)

namespace PConeEB

/-- Lemma 2.5. Let `K` be a pointed closed convex cone, `z ∈ ∂K* \ {0}` with `F := {z}^⊥ ∩ K` a
one-dimensional proper face, `F = {t f | t ≥ 0}` for `f ∈ K \ {0}`. For `η > 0`,
`v ∈ ∂K ∩ B(η) \ F`, `w = P_{{z}^⊥} v`, `u = P_F w`, `u ≠ w`: `⟨f, z⟩ = 0`,
`‖v - w‖ = |⟨z, v⟩| / ‖z‖`; `‖u - w‖ = ‖v - (⟨z,v⟩/‖z‖²) z - (⟨f,v⟩/‖f‖²) f‖` if `⟨f, v⟩ ≥ 0` and
`‖u - w‖ = ‖v - (⟨z,v⟩/‖z‖²) z‖` otherwise; `⟨f, v⟩ ≥ 0` iff `⟨f, w⟩ ≥ 0`, and then
`u = P_{span F} w`; if `⟨f, v⟩ < 0` then `u = 0`.
Lindstrom, Lourenço & Pong, arXiv:2109.11729v4, Lemma 2.5, p.9.

**Formalization Note.** `K*` is `ProperCone.innerDual K`, which requires `[CompleteSpace E]`; this is
automatic in finite dimension. `∂` is `frontier`. Pointed is `K ∩ -K = {0}`. -/
theorem lemma_2_5 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E] {K : Set E} (hK : IsClosedConvexCone K)
    (hpointed : {x | x ∈ K ∧ -x ∈ K} = {0})
    {z : E} (hz : z ∈ frontier ((ProperCone.innerDual K : ProperCone ℝ E) : Set E))
    (hz0 : z ≠ 0) (hproper : K ∩ hyperplane z ≠ K)
    {f : E} (hfK : f ∈ K) (hf0 : f ≠ 0)
    (hF : K ∩ hyperplane z = {x | ∃ t : ℝ, 0 ≤ t ∧ x = t • f})
    {η : ℝ} (hη : 0 < η) {v w u : E} (hv : v ∈ frontier K) (hvη : ‖v‖ ≤ η)
    (hvF : v ∉ K ∩ hyperplane z) (hw : IsProj (hyperplane z) v w)
    (hu : IsProj (K ∩ hyperplane z) w u) (huw : u ≠ w) :
    inner ℝ f z = 0 ∧
      ‖v - w‖ = |inner ℝ z v| / ‖z‖ ∧
      (0 ≤ inner ℝ f v →
        ‖u - w‖ = ‖v - (inner ℝ z v / ‖z‖ ^ 2) • z - (inner ℝ f v / ‖f‖ ^ 2) • f‖) ∧
      (inner ℝ f v < 0 → ‖u - w‖ = ‖v - (inner ℝ z v / ‖z‖ ^ 2) • z‖) ∧
      (0 ≤ inner ℝ f v ↔ 0 ≤ inner ℝ f w) ∧
      (0 ≤ inner ℝ f v →
        IsProj ((Submodule.span ℝ (K ∩ hyperplane z) : Submodule ℝ E) : Set E) w u) ∧
      (inner ℝ f v < 0 → u = 0) := by sorry

end PConeEB
