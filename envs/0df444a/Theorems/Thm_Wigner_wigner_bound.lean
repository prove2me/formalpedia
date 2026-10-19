-- Prove2me | Theorems.Thm_Wigner_wigner_bound
-- name    : Wigner.wigner_bound
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-18T16:52:03.266441+00:00
-- url     : https://prove2.me/theorems/40698555-b834-4465-8581-2215eca924ce
-- title:
--   Pointwise bound $\lvert W(x,p)\rvert \le 2/h$ for pure states
-- statement:
--   The Wigner function of a pure state is bounded pointwise. Let $\psi : \mathbb{R} \to \mathbb{C}$ be a normalized pure state, $\int |\psi|^2 = 1$, and $\hbar > 0$. Then for every phase-space point,
--
--   $$-\frac{2}{h} \le W(x,p) \le \frac{2}{h}, \qquad \text{equivalently} \qquad |W(x,p)| \le \frac{1}{\pi\hbar},$$
--
--   where $h = 2\pi\hbar$ is Planck's constant. This is Property 9 of the source text: by the Cauchy-Schwarz inequality the Wigner function of a pure state is bounded by $2/h$ in absolute value, so it is never a delta spike on phase space — a reflection of the uncertainty principle — and the bound disappears in the classical limit $\hbar \to 0$, where Wigner functions concentrate into delta functions.
--
--   **Formalization Note** The bound is stated with the normalization $1/(\pi\hbar) = 2/h$ used by the definition; it is sharp, attained by Gaussian (coherent) states at their center.
-- source:
--   Wikipedia, "Wigner quasiprobability distribution" (oldid 1376057304), section "Mathematical properties", Property 9. https://en.wikipedia.org/wiki/Wigner_quasiprobability_distribution

import Mathlib
import Definitions.Def_wigner

open MeasureTheory

namespace Wigner

theorem wigner_bound {ψ : ℝ → ℂ} {ℏ x p : ℝ} (hℏ : 0 < ℏ)
    (hnorm : ∫ y, ‖ψ y‖ ^ 2 = 1) :
    |wigner ψ ℏ x p| ≤ 1 / (Real.pi * ℏ) := by sorry

end Wigner
