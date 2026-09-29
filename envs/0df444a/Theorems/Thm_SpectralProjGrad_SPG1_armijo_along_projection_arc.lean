-- Prove2me | Theorems.Thm_SpectralProjGrad_SPG1_armijo_along_projection_arc
-- name    : SpectralProjGrad.SPG1.armijo_along_projection_arc
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T20:51:14.644122+00:00
-- url     : https://prove2.me/theorems/cb9952ce-9b53-46d9-b7ca-3f39dedd7984
-- title:
--   Lemma 2.2 (ii): the Armijo condition holds for small steps along the projection arc
-- statement:
--   Let $\Omega\subseteq\mathbb R^n$ be closed and convex, let $f$ have continuous partial derivatives on an open set $U\supseteq\Omega$, with gradient $g=\nabla f$, let $P$ be the orthogonal projection onto $\Omega$, and let $\gamma\in(0,1)$. Write $g_t(x)=P(x-t\,g(x))-x$. For every $x\in\Omega$ there exists $s_x>0$ such that for all $t\in[0,s_x]$,
--
--   $$
--   f\bigl(P(x-t\,g(x))\bigr)-f(x)\le\gamma\,\langle g(x),g_t(x)\rangle .
--   $$
--
--   This is the Armijo sufficient-decrease condition along the projection arc: every sufficiently short step on the arc achieves at least a fraction $\gamma$ of the first-order predicted decrease. It is what guarantees that the backtracking of SPG1 stops.
--
--   **Formalization Note** The paper defines $g_t$ only for $t>0$; the same formula at $t=0$ gives $g_0(x)=P(x)-x=0$ for $x\in\Omega$, and the Lean statement uses it, so the case $t=0$ reads $0\le0$.
-- source:
--   Birgin, Martínez & Raydan, Nonmonotone Spectral Projected Gradient Methods on Convex Sets, authors' updated version (July 2004) of SIAM J. Optim. 10(4) (2000), https://www.ime.unicamp.br/~martinez/bmr.pdf, p. 5, Lemma 2.2 (ii) (from Bertsekas, Nonlinear Programming (1995), Theorem 2.3.3 (a))

import Mathlib
import Definitions.Def_SpectralProjGrad_Shared_IsProjOnto
import Definitions.Def_SpectralProjGrad_Shared_scaledProjGrad

namespace SpectralProjGrad.SPG1

/-- Lemma 2.2 (ii): for every `x ∈ Ω` there is `s_x > 0` such that for all `t ∈ [0, s_x]`,
`f(P(x - t g(x))) - f(x) ≤ γ ⟨g(x), g_t(x)⟩`, where `g_t(x) = P(x - t g(x)) - x`
(at `t = 0` the same formula gives `g_0(x) = P(x) - x`). -/
theorem armijo_along_projection_arc {n : ℕ}
    {Ω U : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} {γ : ℝ}
    (hΩ_closed : IsClosed Ω) (hΩ_convex : Convex ℝ Ω)
    (hU_open : IsOpen U) (hΩU : Ω ⊆ U) (hf : ContDiffOn ℝ 1 f U)
    (hP : SpectralProjGrad.Shared.IsProjOnto Ω P)
    (hγ : γ ∈ Set.Ioo 0 1)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Ω) :
    ∃ sx : ℝ, 0 < sx ∧ ∀ t ∈ Set.Icc 0 sx,
      f (P (x - t • gradient f x)) - f x ≤ γ * inner ℝ (gradient f x) (SpectralProjGrad.Shared.scaledProjGrad P f t x) := by sorry

end SpectralProjGrad.SPG1
