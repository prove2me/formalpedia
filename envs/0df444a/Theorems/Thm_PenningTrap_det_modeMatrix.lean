-- Prove2me | Theorems.Thm_PenningTrap_det_modeMatrix
-- name    : PenningTrap.det_modeMatrix
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T17:06:31.033976+00:00
-- url     : https://prove2.me/theorems/2fd916a2-3e62-4b36-847f-933acf3dc728
-- title:
--   $\det M(\omega)$ is real and is a cubic in $\omega^2$
-- statement:
--   Let $K$ be a **symmetric** real $3\times3$ matrix, let $b\in\mathbb{R}^3$ be arbitrary (no normalization), and let $\omega_c,\omega$ be real. Then the determinant of the mode matrix is real and depends on $\omega$ only through $\omega^2$:
--
--   $$\det M(\omega)=-q(\omega^2),\qquad q(\lambda)=\det(\lambda I-K)-\omega_c^2\lambda\big(\lambda\langle b,b\rangle-\langle b,Kb\rangle\big).$$
--
--   Two facts are packed into this identity. First, although $M(\omega)$ has imaginary off-diagonal contributions from the magnetic term, its determinant is a real number. Second, that real number is a cubic polynomial evaluated at $\omega^2$, so the trap has at most three distinct squared eigenfrequencies, and their elementary symmetric functions are the coefficients of $q$. The coefficient of $\lambda^2$ in $q$ is $\operatorname{tr}K+\omega_c^2\langle b,b\rangle$, which is where the invariance theorem comes from.
--
--   **Formalization Note.** Symmetry of $K$ is necessary: for a non-symmetric $K$ the determinant acquires a non-zero odd-in-$\omega$ imaginary part.
-- source:
--   X. Fan, T. G. Myers, B. A. D. Sukra, G. Gabrielse, Measurement of the Electron Magnetic Moment, Phys. Rev. Lett. 130, 071801 (2023), arXiv:2209.13084v2, p. 2, Eq. (4) (invariance theorem), with Eq. (2)-(3) for the trap frequencies; original source L. S. Brown and G. Gabrielse, Phys. Rev. A 25, 2423 (1982).

import Mathlib
import Definitions.Def_PenningTrap_model
open Matrix

namespace PenningTrap

theorem det_modeMatrix (K : Matrix (Fin 3) (Fin 3) ℝ) (hK : K.IsSymm) (b : Fin 3 → ℝ)
    (wc w : ℝ) :
    (modeMatrix K b wc w).det = -((charCubic K b wc (w ^ 2) : ℝ) : ℂ) := by sorry

end PenningTrap
