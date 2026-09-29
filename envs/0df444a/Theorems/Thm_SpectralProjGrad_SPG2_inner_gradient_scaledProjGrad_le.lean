-- Prove2me | Theorems.Thm_SpectralProjGrad_SPG2_inner_gradient_scaledProjGrad_le
-- name    : SpectralProjGrad.SPG2.inner_gradient_scaledProjGrad_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T19:00:59.882436+00:00
-- url     : https://prove2.me/theorems/52db0f42-9316-4c25-8491-3a262a4714ff
-- title:
--   Lemma 2.1 (i): $\langle g(x),g_t(x)\rangle\le-\frac1t\|g_t(x)\|_2^2\le-\frac1{\alpha_{\max}}\|g_t(x)\|_2^2$
-- statement:
--   Let $\Omega\subseteq\mathbb R^n$ be closed and convex, let $f$ have continuous partial derivatives on an open set $U\supseteq\Omega$, with gradient $g=\nabla f$, and let $P$ be the orthogonal projection onto $\Omega$. Let $0<\alpha_{\min}<\alpha_{\max}$ and write $g_t(x)=P(x-t\,g(x))-x$. For every $x\in\Omega$ and every $t\in(0,\alpha_{\max}]$,
--
--   $$
--   \langle g(x),g_t(x)\rangle\;\le\;-\frac1t\,\|g_t(x)\|_2^2\;\le\;-\frac1{\alpha_{\max}}\,\|g_t(x)\|_2^2 .
--   $$
--
--   With $t=\alpha_k$ this says that the SPG2 direction $d_k$ is a descent direction whose slope is bounded by its squared length, uniformly over the admissible step range; it is the basic estimate behind the nonmonotone Armijo test (3).
--
--   **Formalization Note** The two inequalities of the chain are stated as a conjunction.
-- source:
--   Birgin, Martínez & Raydan, Nonmonotone Spectral Projected Gradient Methods on Convex Sets, authors' updated version (July 2004) of SIAM J. Optim. 10(4) (2000), https://www.ime.unicamp.br/~martinez/bmr.pdf, p. 5, Lemma 2.1 (i)

import Mathlib
import Definitions.Def_SpectralProjGrad_Shared_IsProjOnto
import Definitions.Def_SpectralProjGrad_Shared_scaledProjGrad

namespace SpectralProjGrad.SPG2

/-- Lemma 2.1 (i): for `x ∈ Ω` and `t ∈ (0, α_max]`,
`⟨g(x), g_t(x)⟩ ≤ -(1/t) ‖g_t(x)‖₂² ≤ -(1/α_max) ‖g_t(x)‖₂²`. -/
theorem inner_gradient_scaledProjGrad_le {n : ℕ}
    {Ω U : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} {αmin αmax : ℝ}
    (hΩ_closed : IsClosed Ω) (hΩ_convex : Convex ℝ Ω)
    (hU_open : IsOpen U) (hΩU : Ω ⊆ U) (hf : ContDiffOn ℝ 1 f U)
    (hP : SpectralProjGrad.Shared.IsProjOnto Ω P)
    (hαmin : 0 < αmin) (hαmin_lt : αmin < αmax)
    (t : ℝ) (ht : t ∈ Set.Ioc 0 αmax)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Ω) :
    inner ℝ (gradient f x) (SpectralProjGrad.Shared.scaledProjGrad P f t x) ≤ -(1 / t) * ‖SpectralProjGrad.Shared.scaledProjGrad P f t x‖ ^ 2 ∧
      -(1 / t) * ‖SpectralProjGrad.Shared.scaledProjGrad P f t x‖ ^ 2 ≤ -(1 / αmax) * ‖SpectralProjGrad.Shared.scaledProjGrad P f t x‖ ^ 2 := by sorry

end SpectralProjGrad.SPG2
