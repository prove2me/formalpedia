-- Prove2me | Theorems.Thm_WeylHeisenbergSIC_fiducial_d_ge_3
-- name    : WeylHeisenbergSIC.fiducial_d_ge_3
-- status  : Open
-- author  : @Mazecto
-- created : 2026-09-21T23:35:39.18293+00:00
-- url     : https://prove2.me/theorems/7d262e49-4c1f-427c-8e38-a74e7f286343
-- title:
--   Zauner's conjecture for dimensions d >= 3
-- statement:
--   For every dimension $d \ge 3$ (qutrits and higher-dimensional qudits), Zauner's conjecture posits the existence of a normalized vector $\psi : \mathbb{Z}/d\mathbb{Z} \to \mathbb{C}$ such that all $(d^2 - 1)$ nonidentity phase-shift displacements $(a, b) \in (\mathbb{Z}/d\mathbb{Z})^2 \setminus \{(0,0)\}$ have squared overlap:
--
--   $$\left| \sum_{x \in \mathbb{Z}/d\mathbb{Z}} \overline{\psi(x)} \chi_b(x) \psi(x+a) \right|^2 = \frac{1}{d+1}.$$
--
--   Zauner additionally conjectured that in every dimension $d \ge 3$, the fiducial vector can be chosen to be an eigenvector of an order-3 canonical unitary operator (the Zauner unitary $U_Z$).
-- source:
--   G. Zauner, Quantendesigns: Grundzüge einer nichtkommutativen Designtheorie, PhD thesis, Univ. Wien (1999); Appleby, SIC-POVMs and the Extended Clifford Group, J. Math. Phys. 46, 052107 (2005).

import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false
noncomputable section
open scoped BigOperators

theorem WeylHeisenbergSIC.fiducial_d_ge_3 (d : ℕ) [NeZero d] (hd : 3 ≤ d) :
    ∃ ψ : ZMod d → ℂ,
      (∑ x : ZMod d, Complex.normSq (ψ x)) = 1 ∧
      ∀ a b : ZMod d, (a,b) ≠ (0,0) →
        Complex.normSq (∑ x : ZMod d, star (ψ x) *
          (ZMod.stdAddChar (b*x) * ψ (x+a))) = (d+1 : ℝ)⁻¹ := by sorry
