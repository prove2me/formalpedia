-- Prove2me | Theorems.Thm_TimeVaryingGames_lemma_A_1
-- name    : TimeVaryingGames.lemma_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:30:17.512743+00:00
-- url     : https://prove2.me/theorems/d54a9030-67ba-47a6-909c-beeb3f00ae91
-- title:
--   Lemma A.1, p.30: subgradient comparison $\langle\nabla h(x),x-p\rangle\le\langle y,x-p\rangle$
-- statement:
--   Let $h$ be a distance-generating function on a compact convex subset $\mathcal C$ of a finite-dimensional normed space, with continuous subgradient selection $\nabla h$ on the prox-domain $\mathcal C_h$. For every $p\in\mathcal C$, every $x\in\mathcal C_h$ and every subgradient $y\in\partial h(x)$,
--   $$\langle\nabla h(x),x-p\rangle\le\langle y,x-p\rangle.$$
--
--   The selected subgradient is the extreme one in every direction pointing into $\mathcal C$; this is what makes the prox step analysis work at boundary points of the prox-domain, where $\partial h(x)$ is not a singleton.
--
--   Differences from the source:
--   - encoding: h : X → ℝ ∪ {∞} with dom h = C; ∂h(x) tested against all x′ ∈ X → h : E → ℝ with only its values on C used; the subgradient inequality tested for x′ ∈ C; reason: h = +∞ off C, so the inequality is automatic off C: the same subdifferential and prox-domain
--   - encoding: there exists a continuous selection ∇h of ∂h on dom ∂h → the selection is a parameter gradh with ContinuousOn and gradh x ∈ ∂h(x) on the prox-domain; reason: D and P are defined through the selection, so it must be fixed data
--   - encoding: K-strongly convex with modulus K (divided by in (A.5b), (40)) → 0 < Kc is part of IsDGF; reason: a strong-convexity modulus is positive; the paper divides by it
-- source:
--   Duvocelle, Mertikopoulos, Staudigl, Vermeulen, Multi-Agent Online Learning in Time-Varying Games, arXiv:1809.03066v3, Appendix A, Lemma A.1, p.30, eq. (A.1)

import Mathlib
import Definitions.Def_TimeVaryingGames_DGF

namespace TimeVaryingGames

/-- **Lemma A.1 (subgradient comparison).**
arXiv:1809.03066v3, Appendix A, p.30: "In what follows, h will denote a distance-generating
function on a compact convex subset C of an d-dimensional normed space X ≅ ℝ^d with dual
Y = X*, as per Definition 1." "Lemma A.1. For all p ∈ C and all y ∈ ∂h(x), x ∈ C_h, we have:
⟨∇h(x), x − p⟩ ≤ ⟨y, x − p⟩. (A.1)" -/
theorem lemma_A_1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {C : Set E} {Kc : ℝ} {h : E → ℝ} {gradh : E → E →L[ℝ] ℝ} (hdgf : IsDGF C Kc h gradh)
    {p : E} (hp : p ∈ C) {x : E} (hx : x ∈ proxDomain C h) {y : E →L[ℝ] ℝ}
    (hy : y ∈ subdiffOn C h x) :
    gradh x (x - p) ≤ y (x - p) := by sorry

end TimeVaryingGames
