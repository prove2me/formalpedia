-- Prove2me | Theorems.Thm_WeylHeisenbergSIC_fiducial_d2_tetrahedron
-- name    : WeylHeisenbergSIC.fiducial_d2_tetrahedron
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-21T23:38:54.433079+00:00
-- url     : https://prove2.me/theorems/63f63a8a-240e-4514-8ec4-d64ce0c015b7
-- title:
--   Existence of fiducial state on ZMod 2
-- statement:
--   In dimension $d = 2$, a qubit fiducial vector $\psi : \mathbb{Z}/2\mathbb{Z} \to \mathbb{C}$ exists whose displacement orbit under the Weyl--Heisenberg group forms a regular tetrahedron of four equiangular unit vectors in $\mathbb{C}^2$, each pair having squared overlap $1/(2+1) = 1/3$.
-- source:
--   Renes, Blume-Kohout, Scott and Caves, Symmetric Informationally Complete Quantum Measurements, J. Math. Phys. 45, 2171 (2004), Section III.A.

import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false
noncomputable section
open scoped BigOperators

theorem WeylHeisenbergSIC.fiducial_d2_tetrahedron :
    ∃ ψ : ZMod 2 → ℂ,
      (∑ x : ZMod 2, Complex.normSq (ψ x)) = 1 ∧
      ∀ a b : ZMod 2, (a,b) ≠ (0,0) →
        Complex.normSq (∑ x : ZMod 2, star (ψ x) *
          (ZMod.stdAddChar (b*x) * ψ (x+a))) = (2+1 : ℝ)⁻¹ := by sorry
