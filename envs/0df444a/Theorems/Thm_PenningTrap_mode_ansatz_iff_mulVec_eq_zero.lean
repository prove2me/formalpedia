-- Prove2me | Theorems.Thm_PenningTrap_mode_ansatz_iff_mulVec_eq_zero
-- name    : PenningTrap.mode_ansatz_iff_mulVec_eq_zero
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T17:04:58.54695+00:00
-- url     : https://prove2.me/theorems/bcc02b4c-85dd-4556-8375-5c7c4c94ce30
-- title:
--   Mode equation: $r(t)=u\,e^{-i\omega t}$ solves the equation of motion iff $M(\omega)u=0$
-- statement:
--   Let $K$ be a real $3\times3$ matrix, $b\in\mathbb{R}^3$, and $\omega_c,\omega$ real numbers, and let $u\in\mathbb{C}^3$ be a complex amplitude. Consider the complex exponential ansatz $r(t)=u\,e^{-i\omega t}$.
--
--   Then $r$ satisfies the equation of motion of a particle in the linear force field $-Kr$ and the magnetic field along $b$,
--
--   $$r''(t)=-K\,r(t)+\omega_c\big(r'(t)\times b\big)\qquad\text{for all }t\in\mathbb{R},$$
--
--   if and only if the amplitude lies in the kernel of the mode matrix:
--
--   $$M(\omega)\,u=0,\qquad M(\omega)=K-\omega^2I-i\,\omega\,\omega_c\,C(b).$$
--
--   This is the step that justifies studying the trap through $M(\omega)$ and its determinant: the normal-mode frequencies of the trap are exactly the $\omega$ for which a non-zero amplitude exists, i.e. for which $\det M(\omega)=0$.
--
--   **Formalization Note.** The equation of motion is stated componentwise with the derivative of a complex-valued function of a real variable, applied twice; $K$ and $b$ act on complex vectors after entrywise coercion. No hypothesis is placed on $K$, $b$, $\omega_c$ or $\omega$.
-- source:
--   X. Fan, T. G. Myers, B. A. D. Sukra, G. Gabrielse, Measurement of the Electron Magnetic Moment, Phys. Rev. Lett. 130, 071801 (2023), arXiv:2209.13084v2, p. 2, Eq. (4) (invariance theorem), with Eq. (2)-(3) for the trap frequencies; original source L. S. Brown and G. Gabrielse, Phys. Rev. A 25, 2423 (1982).

import Mathlib
import Definitions.Def_PenningTrap_model
open Matrix

namespace PenningTrap

theorem mode_ansatz_iff_mulVec_eq_zero (K : Matrix (Fin 3) (Fin 3) ℝ) (b : Fin 3 → ℝ)
    (wc w : ℝ) (u : Fin 3 → ℂ) :
    (∀ t : ℝ, ∀ i : Fin 3,
        deriv (fun s : ℝ => deriv (fun σ : ℝ => u i * Complex.exp (-(Complex.I * w * σ))) s) t
          = -((K.map (fun x : ℝ => (x : ℂ))).mulVec
                (fun j => u j * Complex.exp (-(Complex.I * w * t))) i)
            + (wc : ℂ) *
              crossProduct
                (fun j => deriv (fun σ : ℝ => u j * Complex.exp (-(Complex.I * w * σ))) t)
                (fun j => (b j : ℂ)) i)
      ↔ (modeMatrix K b wc w).mulVec u = 0 := by sorry

end PenningTrap
