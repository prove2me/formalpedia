-- Prove2me | Theorems.Thm_ProbMetricStab_TwoStage_lemma_3_1
-- name    : ProbMetricStab.TwoStage.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:07:17.380593+00:00
-- url     : https://prove2.me/theorems/5f0ba6d6-cfab-4071-8774-96591896551d
-- title:
--   Lemma 3.1, p. 11 — Φ is finite, continuous and piecewise bilinear on the polyhedral cone D × pos W
-- statement:
--   Let $W$ be an $(r,\overline m)$-matrix, $\operatorname{pos}W=\{Wy:y\ge0\}$, $D=\{u:\exists z,\ W'z\le u\}$, and $\Phi(u,t)=\inf\{uy:Wy=t,\ y\ge0\}$.
--
--   Then $D\times\operatorname{pos}W$ is a polyhedral cone in $\mathbb R^{\overline m}\times\mathbb R^r$, $\Phi$ is finite and continuous on it, and there exist $N$, $(r,\overline m)$-matrices $C_1,\dots,C_N$ and polyhedral cones $\mathcal K_1,\dots,\mathcal K_N$ such that
--
--   $$\bigcup_{j=1}^N\mathcal K_j=D\times\operatorname{pos}W,\qquad\operatorname{int}\mathcal K_i\cap\operatorname{int}\mathcal K_j=\emptyset\ (i\ne j),\qquad\Phi(u,t)=C_ju\cdot t\ \text{ for }(u,t)\in\mathcal K_j.$$
--
--   Moreover $\Phi(u,\cdot)$ is convex on $\operatorname{pos}W$ for each $u\in D$, and $\Phi(\cdot,t)$ is concave on $D$ for each $t\in\operatorname{pos}W$.
--
--   This is the structure result for the second-stage value function (Walkup and Wets) on which the regularity of the two-stage integrand in Proposition 3.2 rests.
--
--   **Formalization Note** The page writes the cone as "$\operatorname{pos}W\times D$" and calls it $(\overline m+r)$-dimensional. Since $\Phi(u,t)$ takes $u\in D$ and $t\in\operatorname{pos}W$, the product is read in the order of $\Phi$'s arguments, $D\times\operatorname{pos}W$, and "$(\overline m+r)$-dimensional polyhedral cone" is read as "polyhedral cone in $\mathbb R^{\overline m+r}$" ($\operatorname{pos}W$ need not be full-dimensional). Finiteness is $\Phi\ne\pm\infty$; continuity is that of the $\overline{\mathbb R}$-valued function on the cone; convexity and concavity are stated for the real values, which is legitimate because $\Phi$ is finite there.
-- source:
--   Rachev & Römisch, Quantitative stability in stochastic programming: The method of probability metrics, preprint (edoc.hu-berlin.de), p. 11, Lemma 3.1

import Mathlib
import Definitions.Def_ProbMetricStab_TwoStage_Model

open Matrix

namespace ProbMetricStab.TwoStage

/-- Lemma 3.1 (p. 11, after Walkup–Wets): `Φ` is finite and continuous on the polyhedral cone
`D × pos W ⊆ ℝ^{m̄} × ℝ^r`; there are `(r, m̄)`-matrices `C_j` and polyhedral cones `𝒦_j`,
`j = 1, …, N`, covering `D × pos W` with pairwise disjoint interiors, such that
`Φ(u, t) = C_j u · t` on `𝒦_j`; and `Φ(u, ·)` is convex on `pos W` for `u ∈ D`, `Φ(·, t)` is
concave on `D` for `t ∈ pos W`. -/
theorem lemma_3_1 {r mbar : ℕ} (W : Matrix (Fin r) (Fin mbar) ℝ) :
    IsPolyhedralCone (D W ×ˢ posW W) ∧
    (∀ p ∈ D W ×ˢ posW W, Phi W p.1 p.2 ≠ ⊤ ∧ Phi W p.1 p.2 ≠ ⊥) ∧
    ContinuousOn (fun p : (Fin mbar → ℝ) × (Fin r → ℝ) => Phi W p.1 p.2) (D W ×ˢ posW W) ∧
    (∃ (N : ℕ) (C : Fin N → Matrix (Fin r) (Fin mbar) ℝ)
        (K : Fin N → Set ((Fin mbar → ℝ) × (Fin r → ℝ))),
      (∀ j, IsPolyhedralCone (K j)) ∧
      (⋃ j, K j) = D W ×ˢ posW W ∧
      (∀ i j, i ≠ j → interior (K i) ∩ interior (K j) = ∅) ∧
      ∀ j, ∀ p ∈ K j, Phi W p.1 p.2 = (((C j *ᵥ p.1) ⬝ᵥ p.2 : ℝ) : EReal)) ∧
    (∀ u ∈ D W, ConvexOn ℝ (posW W) (fun t => (Phi W u t).toReal)) ∧
    (∀ t ∈ posW W, ConcaveOn ℝ (D W) (fun u => (Phi W u t).toReal)) := by sorry

end ProbMetricStab.TwoStage
