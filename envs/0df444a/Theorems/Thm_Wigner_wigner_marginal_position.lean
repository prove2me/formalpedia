-- Prove2me | Theorems.Thm_Wigner_wigner_marginal_position
-- name    : Wigner.wigner_marginal_position
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-18T16:50:03.089648+00:00
-- url     : https://prove2.me/theorems/0bccfa30-980a-4e03-a338-b0acde95ac65
-- title:
--   Position-space marginal of the Wigner function
-- statement:
--   Integrating the Wigner function over momentum recovers the position probability density. Let $\psi : \mathbb{R} \to \mathbb{C}$ be a Schwartz function, $\hbar > 0$, and $x \in \mathbb{R}$. Then
--
--   $$\int_{-\infty}^{\infty} W(x, p)\,dp = |\psi(x)|^2,$$
--
--   where $W$ is the Wigner function of $\psi$. For a pure state, $|\psi(x)|^2$ is the probability density of finding the particle at position $x$, so the momentum-marginal of the Wigner function is exactly the Born position distribution. This is the first marginal identity of Property 2 in the source text, $\int dp\, W(x,p) = \langle x|\hat\rho|x\rangle$, which for a pure state reads $\langle x|\hat\rho|x\rangle = |\psi(x)|^2$.
--
--   **Formalization Note** Schwartz regularity is assumed so that the identity holds at every point $x$; it is the standing regularity convention of the source. The integral over $p$ is a Lebesgue (Bochner) integral of a real-valued function.
-- source:
--   Wikipedia, "Wigner quasiprobability distribution" (oldid 1376057304), section "Mathematical properties", Property 2, first marginal formula. https://en.wikipedia.org/wiki/Wigner_quasiprobability_distribution

import Mathlib
import Definitions.Def_wigner

open MeasureTheory

namespace Wigner

theorem wigner_marginal_position (ψ : SchwartzMap ℝ ℂ) {ℏ x : ℝ} (hℏ : 0 < ℏ) :
    ∫ p, wigner (⇑ψ) ℏ x p = ‖⇑ψ x‖ ^ 2 := by sorry

end Wigner
