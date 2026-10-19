-- Prove2me | Theorems.Thm_Wigner_hudson
-- name    : Wigner.hudson
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-18T16:52:46.466481+00:00
-- url     : https://prove2.me/theorems/c736dca5-241c-47dd-ad40-d8a301cc0436
-- title:
--   Hudson's theorem
-- statement:
--   Hudson's theorem: the only pure states whose Wigner functions are nonnegative are Gaussian wave packets. Let $\psi : \mathbb{R} \to \mathbb{C}$ be a normalized pure state, $\int_{\mathbb{R}} |\psi|^2 = 1$, and $\hbar > 0$. If
--
--   $$W(x,p) \ge 0 \quad \text{for all } (x,p) \in \mathbb{R}^2,$$
--
--   then there exist complex numbers $a, b, c$ with $\mathrm{Re}(a) > 0$ such that
--
--   $$\psi(x) = e^{-ax^2 + bx + c}$$
--
--   for almost every $x$. This is the source text's characterization, proved by R. L. Hudson (1974) and extended to higher dimensions by Soto and Claverie (1983): a one-dimensional pure state has an everywhere nonnegative Wigner function if and only if it is a Gaussian wave packet. It delimits exactly which quantum states admit a classical phase-space probability description.
--
--   **Formalization Note** The conclusion holds almost everywhere: the Wigner function is insensitive to changes of $\psi$ on a Lebesgue-null set, so no pointwise conclusion is possible; this is the faithful reading of the source's "the wave function must have the form". No minimum-uncertainty property is claimed (the source explicitly notes that nonnegative-Wigner pure states need not be minimum-uncertainty states in Heisenberg's sense).
-- source:
--   Wikipedia, "Wigner quasiprobability distribution" (oldid 1376057304), section "Positivity of the function" (Hudson's theorem). Primary source: R. L. Hudson, Reports on Mathematical Physics 6(2), 249-252 (1974), doi:10.1016/0034-4877(74)90007-X. https://en.wikipedia.org/wiki/Wigner_quasiprobability_distribution

import Mathlib
import Definitions.Def_wigner

open MeasureTheory

namespace Wigner

theorem hudson {ψ : ℝ → ℂ} {ℏ : ℝ} (hℏ : 0 < ℏ)
    (hnorm : ∫ y, ‖ψ y‖ ^ 2 = 1)
    (hW : ∀ x p, 0 ≤ wigner ψ ℏ x p) :
    ∃ a b c : ℂ, 0 < Complex.re a ∧
      ∀ᵐ y ∂volume, ψ y = Complex.exp (-(a * (y : ℂ) ^ 2) + b * (y : ℂ) + c) := by sorry

end Wigner
