-- Prove2me | Theorems.Thm_PorteusSS_leibniz_exp_kernel
-- name    : PorteusSS.leibniz_exp_kernel
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T17:54:47.101888+00:00
-- url     : https://prove2.me/theorems/82dfc03d-bf32-4996-b548-3b2573accc2f
-- title:
--   Lemma 5 — differentiating a convolution with an exponential kernel
-- statement:
--   Let $g : \mathbb R \to \mathbb R$ be continuous and $\lambda > 0$, and suppose that the integral
--   $$ f(x) = \int_0^\infty g(x - t)\, \lambda e^{-\lambda t}\, dt $$
--   exists (is finite) for every $x \in \mathbb R$. Then $f$ is continuously differentiable on $\mathbb R$ and
--   $$ f'(x) = \lambda\,[\,g(x) - f(x)\,] \qquad (23) $$
--   for every $x \in \mathbb R$.
--
--   The identity (23) is what drives the analysis of convolutions with exponential densities: the smoothed function moves toward $g$ at rate $\lambda$, so its local extrema occur where it crosses $g$.
--
--   **Formalization Note.** "$f$ exists" is read as Lebesgue integrability of $t \mapsto g(x-t)\lambda e^{-\lambda t}$ on $[0,\infty)$ for every $x$.
-- source:
--   Porteus, On the Optimality of Generalized (s, S) Policies, Management Science 17(7):411–426 (1971), p. 422, Lemma 5

import Mathlib

open MeasureTheory Filter Topology Set

namespace PorteusSS

/-- Lemma 5 (p. 422). If `g` is continuous on `ℝ`, `lam > 0`, and
`f(x) = ∫_0^∞ g(x - t) lam e^{-lam t} dt` exists (is finite) for every `x`, then `f` is
continuously differentiable on `ℝ` and `f'(x) = lam (g(x) - f(x))`  (23). -/
theorem leibniz_exp_kernel (g : ℝ → ℝ) (lam : ℝ) (hlam : 0 < lam) (hg : Continuous g)
    (hint : ∀ x : ℝ,
      IntegrableOn (fun t => g (x - t) * (lam * Real.exp (-lam * t))) (Ici 0)) :
    ContDiff ℝ 1 (fun x => ∫ t in Ici (0 : ℝ), g (x - t) * (lam * Real.exp (-lam * t))) ∧
      ∀ x : ℝ, HasDerivAt (fun x => ∫ t in Ici (0 : ℝ), g (x - t) * (lam * Real.exp (-lam * t)))
        (lam * (g x - ∫ t in Ici (0 : ℝ), g (x - t) * (lam * Real.exp (-lam * t)))) x := by sorry

end PorteusSS
