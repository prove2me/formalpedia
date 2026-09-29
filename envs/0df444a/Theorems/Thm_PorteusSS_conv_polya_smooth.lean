-- Prove2me | Theorems.Thm_PorteusSS_conv_polya_smooth
-- name    : PorteusSS.conv_polya_smooth
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T17:55:28.370465+00:00
-- url     : https://prove2.me/theorems/eb6f8835-085d-4197-93ca-f86f82e34a64
-- title:
--   Lemma 6 — smoothness of $g * \varphi$ for a one-sided Pólya density $\varphi$
-- statement:
--   Let $g$ be piecewise continuous and PF-integrable on $\mathbb R$, let $\varphi$ be a one-sided Pólya density, and let $f = g * \varphi$, i.e.
--   $$ f(x) = \int_{-\infty}^{\infty} g(x - t)\,\varphi(t)\,dt . $$
--   Then
--
--   1. $f$ is continuous on $\mathbb R$;
--   2. $f$ is continuously differentiable on $\mathbb R$ except on a finite set;
--   3. if $\varphi$ is the exponential density with parameter $\lambda > 0$, then $f'(x) = \lambda[g(x) - f(x)]$ (eq. (23)) at every point $x$ where $g$ is continuous.
--
--   This lemma supplies the continuity of $h_n$ in the inductive step (Lemma 3) and the differential identity used for Lemma 10.
--
--   **Formalization Note.** "Continuously differentiable except on a finite set" is: there is a finite set $A$ such that $f$ is $C^1$ in a neighbourhood of every $x \notin A$.
-- source:
--   Porteus, On the Optimality of Generalized (s, S) Policies, Management Science 17(7):411–426 (1971), p. 422, Lemma 6

import Mathlib
import Definitions.Def_PorteusSS_Functions

open MeasureTheory Filter Topology Set

namespace PorteusSS

/-- Lemma 6 (p. 422). If `g` is piecewise continuous and PF-integrable on `ℝ` and `φ` is a
one-sided Pólya density, then `g * φ` is continuous on `ℝ` and continuously differentiable
outside a finite set; and if `φ` is the exponential density with parameter `lam > 0`, then
`(g * φ)'(x) = lam (g(x) - (g * φ)(x))` at every point `x` where `g` is continuous. -/
theorem conv_polya_smooth (g φ : ℝ → ℝ) (hg_pc : PiecewiseContinuousOn g univ)
    (hg_pf : PFIntegrable g) (hφ : IsOneSidedPolyaDensity φ) :
    Continuous (conv g φ) ∧
      (∃ A : Finset ℝ, ∀ x : ℝ, x ∉ A → ContDiffAt ℝ 1 (conv g φ) x) ∧
      (∀ lam : ℝ, 0 < lam → φ = expDensity lam → ∀ x : ℝ, ContinuousAt g x →
        HasDerivAt (conv g φ) (lam * (g x - conv g φ x)) x) := by sorry

end PorteusSS
