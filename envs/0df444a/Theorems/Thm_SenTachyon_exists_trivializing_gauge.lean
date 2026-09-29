-- Prove2me | Theorems.Thm_SenTachyon_exists_trivializing_gauge
-- name    : SenTachyon.exists_trivializing_gauge
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T19:21:17.202986+00:00
-- url     : https://prove2.me/theorems/219ba1e3-8f06-4a00-a4cd-c0086a57668c
-- title:
--   Eq. (8): existence of a gauge transformation trivializing Ω₁, Ω₂
-- statement:
--   Let $\tilde R_1,\tilde R_2>0$. There is a smooth map $g$ from the plane to $2\times2$ complex matrices, taking values in $SU(2)$ on the rectangle $[0,2\pi\tilde R_1]\times[0,2\pi\tilde R_2]$, such that
--   1. $g(0,x^2)=\exp(ix^2\sigma_3/\tilde R_2)$ for $x^2\in[0,2\pi\tilde R_2]$;
--   2. $g(2\pi\tilde R_1,x^2)=1$ for $x^2\in[0,2\pi\tilde R_2]$;
--   3. $g(x^1,2\pi\tilde R_2)=g(x^1,0)$ for $x^1\in[0,2\pi\tilde R_1]$;
--   4. $\dfrac{\partial g}{\partial x^1}(x^1,x^2)=0$ at $x^1=0$ and $x^1=2\pi\tilde R_1$, for $x^2\in[0,2\pi\tilde R_2]$.
--
--   Such a $g$ turns both transition functions into the identity, so the transformed field is periodic; the paper deduces existence from the simple connectivity of $SU(2)$.
--
--   **Formalization Note** Smoothness is required of every matrix entry as a function on all of $\mathbb R^2$ (a smooth extension beyond the rectangle), which lets the boundary derivative in item 4 be the ordinary partial derivative.
-- source:
--   A. Sen, Tachyon condensation on the brane antibrane system, JHEP 08 (1998) 012, arXiv:hep-th/9805170, https://doi.org/10.1088/1126-6708/1998/08/012, p. 2, eq. (8) and the following paragraph

import Mathlib
import Definitions.Def_SenTachyon_Defs

open scoped ContDiff
open Filter Topology

namespace SenTachyon
theorem exists_trivializing_gauge (R₁t R₂t : ℝ) (h₁ : 0 < R₁t) (h₂ : 0 < R₂t) :
    ∃ g : ℝ × ℝ → Matrix (Fin 2) (Fin 2) ℂ,
      (∀ i j, ContDiff ℝ ∞ (fun x => g x i j)) ∧
      (∀ x ∈ Set.Icc 0 (2 * Real.pi * R₁t) ×ˢ Set.Icc 0 (2 * Real.pi * R₂t),
        g x ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) ∧
      (∀ x₂ ∈ Set.Icc 0 (2 * Real.pi * R₂t), g (0, x₂) = omega1 R₂t (0, x₂)) ∧
      (∀ x₂ ∈ Set.Icc 0 (2 * Real.pi * R₂t), g (2 * Real.pi * R₁t, x₂) = 1) ∧
      (∀ x₁ ∈ Set.Icc 0 (2 * Real.pi * R₁t), g (x₁, 2 * Real.pi * R₂t) = g (x₁, 0)) ∧
      (∀ x₂ ∈ Set.Icc 0 (2 * Real.pi * R₂t),
        partialDeriv 0 g (0, x₂) = 0 ∧ partialDeriv 0 g (2 * Real.pi * R₁t, x₂) = 0) := by sorry
end SenTachyon
