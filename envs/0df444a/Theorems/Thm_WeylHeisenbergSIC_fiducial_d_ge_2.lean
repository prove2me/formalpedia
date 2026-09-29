-- Prove2me | Theorems.Thm_WeylHeisenbergSIC_fiducial_d_ge_2
-- name    : WeylHeisenbergSIC.fiducial_d_ge_2
-- status  : Open
-- author  : @Mazecto
-- created : 2026-09-21T23:30:35.200472+00:00
-- url     : https://prove2.me/theorems/69c7664d-5916-4b1e-a3c4-6f185761aed1
-- title:
--   Zauner's conjecture for dimensions d >= 2
-- statement:
--   For every dimension $d \ge 2$, Zauner's conjecture posits the existence of a normalized fiducial vector $\psi : \mathbb{Z}/d\mathbb{Z} \to \mathbb{C}$ such that for all nonidentity displacements $(a, b) \in (\mathbb{Z}/d\mathbb{Z})^2 \setminus \{(0,0)\}$, the squared overlap between $\psi$ and its Weyl--Heisenberg displacement operator equals:
--
--   $$\left| \sum_{x \in \mathbb{Z}/d\mathbb{Z}} \overline{\psi(x)} \chi_b(x) \psi(x+a) \right|^2 = \frac{1}{d+1}.$$
--
--   This constitutes the non-vacuous core of Zauner's conjecture for all quantum systems of dimension two or higher.
-- source:
--   G. Zauner, Quantendesigns: Grundzüge einer nichtkommutativen Designtheorie, PhD thesis, Univ. Wien (1999); Renes et al., J. Math. Phys. 45, 2171 (2004).

import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false
noncomputable section
open scoped BigOperators

theorem WeylHeisenbergSIC.fiducial_d_ge_2 (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ ψ : ZMod d → ℂ,
      (∑ x : ZMod d, Complex.normSq (ψ x)) = 1 ∧
      ∀ a b : ZMod d, (a,b) ≠ (0,0) →
        Complex.normSq (∑ x : ZMod d, star (ψ x) *
          (ZMod.stdAddChar (b*x) * ψ (x+a))) = (d+1 : ℝ)⁻¹ := by sorry
