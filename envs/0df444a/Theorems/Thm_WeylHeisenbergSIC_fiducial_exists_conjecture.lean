-- Prove2me | Theorems.Thm_WeylHeisenbergSIC_fiducial_exists_conjecture
-- name    : WeylHeisenbergSIC.fiducial_exists_conjecture
-- status  : Open
-- author  : @Mazecto
-- created : 2026-09-21T23:16:02.890849+00:00
-- url     : https://prove2.me/theorems/9ebb1be2-3e5a-43c7-892f-ae723b8e03fa
-- title:
--   Zauner's conjecture on Weyl-Heisenberg fiducial vector existence
-- statement:
--   Zauner's conjecture states that for every positive dimension $d \ge 1$, there exists a normalized fiducial vector $\psi : \mathbb{Z}/d\mathbb{Z} \to \mathbb{C}$ such that for all nonidentity Weyl--Heisenberg displacement pairs $(a, b) \in (\mathbb{Z}/d\mathbb{Z})^2 \setminus \{(0,0)\}$, the squared inner product between $\psi$ and its displaced copy satisfies:
--
--   $$\left| \sum_{x \in \mathbb{Z}/d\mathbb{Z}} \overline{\psi(x)} \chi_b(x) \psi(x+a) \right|^2 = \frac{1}{d+1}$$
--
--   where $\chi_b(x) = \exp(2\pi i b x / d)$ is the standard additive character on $\mathbb{Z}/d\mathbb{Z}$.
-- source:
--   Renes, Blume-Kohout, Scott and Caves, Symmetric Informationally Complete Quantum Measurements, J. Math. Phys. 45, 2171 (2004), https://arxiv.org/abs/quant-ph/0310075

import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false
noncomputable section
open scoped BigOperators

theorem WeylHeisenbergSIC.fiducial_exists_conjecture (d : ℕ) [NeZero d] :
    ∃ ψ : ZMod d → ℂ,
      (∑ x : ZMod d, Complex.normSq (ψ x)) = 1 ∧
      ∀ a b : ZMod d, (a,b) ≠ (0,0) →
        Complex.normSq (∑ x : ZMod d, star (ψ x) *
          (ZMod.stdAddChar (b*x) * ψ (x+a))) = (d+1 : ℝ)⁻¹ := by sorry
