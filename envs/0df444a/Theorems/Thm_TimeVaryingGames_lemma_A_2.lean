-- Prove2me | Theorems.Thm_TimeVaryingGames_lemma_A_2
-- name    : TimeVaryingGames.lemma_A_2
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T13:30:18.877295+00:00
-- url     : https://prove2.me/theorems/b14620ad-c1ce-4f41-885f-faf8b3cbe1a6
-- title:
--   Lemma A.2, p.30: the three-point identity for the Bregman divergence
-- statement:
--   Let $h$ be a distance-generating function on a compact convex set $\mathcal C$ with selection $\nabla h$ and Bregman divergence $D$. For all $p\in\mathcal C$ and all $x,x'$ in the prox-domain $\mathcal C_h$,
--   $$D(p,x)=D(p,x')+D(x',x)+\langle\nabla h(x)-\nabla h(x'),x'-p\rangle.$$
--
--   The identity compares the divergence to a base point before and after a move from $x$ to $x'$; it is the algebraic core of the one-step estimate for the prox-mapping.
--
--   Differences from the source:
--   - encoding: h : X → ℝ ∪ {∞} with dom h = C; ∂h(x) tested against all x′ ∈ X → h : E → ℝ with only its values on C used; the subgradient inequality tested for x′ ∈ C; reason: h = +∞ off C, so the inequality is automatic off C: the same subdifferential and prox-domain
--   - encoding: there exists a continuous selection ∇h of ∂h on dom ∂h → the selection is a parameter gradh with ContinuousOn and gradh x ∈ ∂h(x) on the prox-domain; reason: D and P are defined through the selection, so it must be fixed data
--   - encoding: K-strongly convex with modulus K (divided by in (A.5b), (40)) → 0 < Kc is part of IsDGF; reason: a strong-convexity modulus is positive; the paper divides by it
-- source:
--   Duvocelle, Mertikopoulos, Staudigl, Vermeulen, Multi-Agent Online Learning in Time-Varying Games, arXiv:1809.03066v3, Appendix A, Lemma A.2, p.30, eq. (A.3)

import Mathlib
import Definitions.Def_TimeVaryingGames_DGF

namespace TimeVaryingGames

/-- **Lemma A.2 (3-point identity).**
arXiv:1809.03066v3, Appendix A, p.30: "Lemma A.2 (3-point identity). For all p ∈ C and all
x, x' ∈ C_h, we have: D(p, x) = D(p, x') + D(x', x) + ⟨∇h(x) − ∇h(x'), x' − p⟩. (A.3)"
(with `h` a DGF on the compact convex `C`, as throughout Appendix A). -/
theorem lemma_A_2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {C : Set E} {Kc : ℝ} {h : E → ℝ} {gradh : E → E →L[ℝ] ℝ} (hdgf : IsDGF C Kc h gradh)
    {p : E} (hp : p ∈ C) {x x' : E} (hx : x ∈ proxDomain C h) (hx' : x' ∈ proxDomain C h) :
    bregman h gradh p x =
      bregman h gradh p x' + bregman h gradh x' x + (gradh x - gradh x') (x' - p) := by sorry

end TimeVaryingGames
