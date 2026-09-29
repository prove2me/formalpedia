-- Prove2me | Theorems.Thm_WeylHeisenbergSIC_fiducial_d2_explicit
-- name    : WeylHeisenbergSIC.fiducial_d2_explicit
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-21T23:41:04.191183+00:00
-- url     : https://prove2.me/theorems/dfdb3cb8-c4f2-4d3f-bd3b-679d75f2d213
-- title:
--   Explicit fiducial vector on ZMod 2
-- statement:
--   An explicit qubit fiducial vector $\psi : \mathbb{Z}/2\mathbb{Z} \to \mathbb{C}$ for the Weyl--Heisenberg group is given by setting the amplitude ratios to match the vertices of a regular tetrahedron inscribed in the Bloch sphere:
--
--   $$\psi(0) = \cos(\theta/2), \quad \psi(1) = e^{i\pi/4} \sin(\theta/2)$$
--
--   where $\cos\theta = 1/\sqrt{3}$. Its norm is $1$ and its overlaps with all nonidentity displacements satisfy $|\langle \psi, D(a,b) \psi \rangle|^2 = 1/3$.
-- source:
--   Renes, Blume-Kohout, Scott and Caves, Symmetric Informationally Complete Quantum Measurements, J. Math. Phys. 45, 2171 (2004), Section III.A.

import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false
noncomputable section
open scoped BigOperators

theorem WeylHeisenbergSIC.fiducial_d2_explicit :
    ∃ ψ : ZMod 2 → ℂ,
      (∑ x : ZMod 2, Complex.normSq (ψ x)) = 1 ∧
      ∀ a b : ZMod 2, (a,b) ≠ (0,0) →
        Complex.normSq (∑ x : ZMod 2, star (ψ x) *
          (ZMod.stdAddChar (b*x) * ψ (x+a))) = (2+1 : ℝ)⁻¹ := by sorry
