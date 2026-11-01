-- Prove2me | Theorems.Thm_TimeVaryingGames_lemma_A_3
-- name    : TimeVaryingGames.lemma_A_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:30:21.268055+00:00
-- url     : https://prove2.me/theorems/e0a5c551-7f11-40ed-95fe-1a42648213d1
-- title:
--   Lemma A.3, pp.30–31: one prox step, (A.5a)–(A.5b)
-- statement:
--   Let $h$ be a distance-generating function with modulus $K$ on a compact convex set $\mathcal C$, with selection $\nabla h$, Bregman divergence $D$ and prox-mapping $\mathcal P$. Fix $p\in\mathcal C$, $x$ in the prox-domain $\mathcal C_h$, a dual vector $y$, and let $x^+=\mathcal P(x;y)$. Then $x^+\in\mathcal C_h$ and
--   $$D(p,x^+)\le D(p,x)-D(x^+,x)+\langle y,x^+-p\rangle\le D(p,x)+\langle y,x-p\rangle+\frac1{2K}\|y\|_*^2.$$
--
--   This is the basic one-step estimate of mirror descent: it bounds the divergence to any fixed point after a prox step, and $x^+\in\mathcal C_h$ makes it applicable again at the next step.
--
--   Differences from the source:
--   - generalization: the conclusion (A.5a)–(A.5b) → also x⁺ ∈ C_h as a first conjunct; reason: the paper's proof establishes it ("This means that x⁺ ∈ dom ∂h ≡ C_h"); dropping the conjunct gives the printed statement
--   - encoding: h : X → ℝ ∪ {∞} with dom h = C; ∂h(x) tested against all x′ ∈ X → h : E → ℝ with only its values on C used; the subgradient inequality tested for x′ ∈ C; reason: h = +∞ off C, so the inequality is automatic off C: the same subdifferential and prox-domain
--   - encoding: there exists a continuous selection ∇h of ∂h on dom ∂h → the selection is a parameter gradh with ContinuousOn and gradh x ∈ ∂h(x) on the prox-domain; reason: D and P are defined through the selection, so it must be fixed data
--   - encoding: the prox-mapping P(x; y) = argmin (13) as a function → the relation IsProxPoint (xp ∈ C minimizes (13)); reason: the minimizer exists and is unique for a DGF, so the relation is the graph of P
--   - encoding: K-strongly convex with modulus K (divided by in (A.5b), (40)) → 0 < Kc is part of IsDGF; reason: a strong-convexity modulus is positive; the paper divides by it
-- source:
--   Duvocelle, Mertikopoulos, Staudigl, Vermeulen, Multi-Agent Online Learning in Time-Varying Games, arXiv:1809.03066v3, Appendix A, Lemma A.3, pp.30–31, eqs. (A.4), (A.5a), (A.5b)

import Mathlib
import Definitions.Def_TimeVaryingGames_DGF

namespace TimeVaryingGames

/-- **Lemma A.3 (one prox-step).**
arXiv:1809.03066v3, Appendix A, pp.30–31: "Lemma A.3. Fix some p ∈ C and consider the recursive
update rule x⁺ = P(x; y) (A.4) for x ∈ C_h, y ∈ Y. Then:
D(p, x⁺) ≤ D(p, x) − D(x⁺, x) + ⟨y, x⁺ − p⟩ (A.5a)
≤ D(p, x) + ⟨y, x − p⟩ + (1/2K)‖y‖²_*. (A.5b)"

The conclusion is the chain (A.5a)–(A.5b) together with `x⁺ ∈ C_h`, which the paper's proof
establishes ("This means that x⁺ ∈ dom ∂h ≡ C_h") and which makes the update rule recursive.

**Formalization Note.** `x⁺ = P(x; y)` is the relation `IsProxPoint C h gradh x y xp`;
`‖y‖_*` is the operator norm of `y : E →L[ℝ] ℝ`. -/
theorem lemma_A_3 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {C : Set E} {Kc : ℝ} {h : E → ℝ} {gradh : E → E →L[ℝ] ℝ} (hdgf : IsDGF C Kc h gradh)
    {p : E} (hp : p ∈ C) {x : E} (hx : x ∈ proxDomain C h) (y : E →L[ℝ] ℝ) {xp : E}
    (hxp : IsProxPoint C h gradh x y xp) :
    xp ∈ proxDomain C h ∧
      bregman h gradh p xp ≤ bregman h gradh p x - bregman h gradh xp x + y (xp - p) ∧
      bregman h gradh p x - bregman h gradh xp x + y (xp - p) ≤
        bregman h gradh p x + y (x - p) + 1 / (2 * Kc) * ‖y‖ ^ 2 := by sorry

end TimeVaryingGames
