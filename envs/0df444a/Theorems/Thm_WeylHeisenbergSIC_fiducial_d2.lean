-- Prove2me | Theorems.Thm_WeylHeisenbergSIC_fiducial_d2
-- name    : WeylHeisenbergSIC.fiducial_d2
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-21T23:35:34.127419+00:00
-- url     : https://prove2.me/theorems/d30f73c9-85cf-4ff6-a7ce-7e76093a3b19
-- title:
--   Existence of Weyl-Heisenberg fiducial vector in dimension 2
-- statement:
--   In dimension $d = 2$ (the qubit setting), a Weyl--Heisenberg fiducial state exists. An explicit normalized vector $\psi : \mathbb{Z}/2\mathbb{Z} \to \mathbb{C}$ is given by:
--
--   $$\psi(0) = \sqrt{\frac{1 + 1/\sqrt{3}}{2}}, \quad \psi(1) = \sqrt{\frac{1 - 1/\sqrt{3}}{2}} \, e^{i\pi/4}.$$
--
--   Its squared norm satisfies $|\psi(0)|^2 + |\psi(1)|^2 = 1$, and its overlap with each of the three nonidentity Weyl--Heisenberg displacements $(a, b) \in \{(0, 1), (1, 0), (1, 1)\}$ has squared modulus exactly equal to $1/(2+1) = 1/3$. The orbit under the displacement group generates the vertices of a regular tetrahedron inscribed in the Bloch sphere.
-- source:
--   Renes, Blume-Kohout, Scott and Caves, Symmetric Informationally Complete Quantum Measurements, J. Math. Phys. 45, 2171 (2004), Section III.A.

import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false
noncomputable section
open scoped BigOperators

theorem WeylHeisenbergSIC.fiducial_d2 :
    ∃ ψ : ZMod 2 → ℂ,
      (∑ x : ZMod 2, Complex.normSq (ψ x)) = 1 ∧
      ∀ a b : ZMod 2, (a,b) ≠ (0,0) →
        Complex.normSq (∑ x : ZMod 2, star (ψ x) *
          (ZMod.stdAddChar (b*x) * ψ (x+a))) = (2+1 : ℝ)⁻¹ := by sorry
