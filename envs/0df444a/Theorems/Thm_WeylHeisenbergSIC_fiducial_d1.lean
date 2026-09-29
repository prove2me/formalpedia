-- Prove2me | Theorems.Thm_WeylHeisenbergSIC_fiducial_d1
-- name    : WeylHeisenbergSIC.fiducial_d1
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-21T23:30:34.02256+00:00
-- url     : https://prove2.me/theorems/0d3e478d-93cb-494e-9f01-065c93c966dc
-- title:
--   Existence of Weyl-Heisenberg fiducial vector in dimension 1
-- statement:
--   In dimension $d = 1$, the vector space is $\mathbb{C}^1 \cong \mathbb{C}$, indexed by the singleton group $\mathbb{Z}/1\mathbb{Z} \cong \{0\}$. Choosing the unit vector $\psi(0) = 1$ gives:
--
--   $$\sum_{x \in \mathbb{Z}/1\mathbb{Z}} |\psi(x)|^2 = |\psi(0)|^2 = 1.$$
--
--   Furthermore, on $\mathbb{Z}/1\mathbb{Z}$, the only element is $0$, so the condition $(a, b) \ne (0, 0)$ is vacuous. Therefore, $\psi(0) = 1$ trivially constitutes a normalized Weyl--Heisenberg fiducial vector in dimension 1.
-- source:
--   Renes, Blume-Kohout, Scott and Caves, Symmetric Informationally Complete Quantum Measurements, J. Math. Phys. 45, 2171 (2004), Section III.

import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false
noncomputable section
open scoped BigOperators

theorem WeylHeisenbergSIC.fiducial_d1 :
    ∃ ψ : ZMod 1 → ℂ,
      (∑ x : ZMod 1, Complex.normSq (ψ x)) = 1 ∧
      ∀ a b : ZMod 1, (a,b) ≠ (0,0) →
        Complex.normSq (∑ x : ZMod 1, star (ψ x) *
          (ZMod.stdAddChar (b*x) * ψ (x+a))) = (1+1 : ℝ)⁻¹ := by sorry
