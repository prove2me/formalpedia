-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P01_tensorPower_partialTranspose_stability
-- name    : QAlgorithms.Papers.Independent.Independent1.P01.tensorPower_partialTranspose_stability
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:05:59.355438+00:00
-- url     : https://prove2.me/theorems/d744b49e-15c7-436f-b05b-35ec03a38e1d
-- title:
--   Identical tensor copies do not strengthen the PPT test
-- statement:
--   Let $\rho$ be a density matrix on two nonempty finite subsystem spaces $I$ and $J$, and let $k\ge1$. Group the $k$ copies so that the first observer holds all $I$ registers and the second holds all $J$ registers. In these coordinates let $\rho^{[k]}$ denote the product with entries $\prod_{t=1}^k\rho_{i_tj_t,i'_tj'_t}$, and put $\sigma=\rho^{T_I}$. Then
--
--   $$\rho\text{ separable}\ \Longrightarrow\ \rho^{[k]}\text{ separable},\qquad (\rho^{[k]})^{T_{I^k}}=\sigma^{[k]},\qquad \sigma\succeq0\ \Longrightarrow\ (\rho^{[k]})^{T_{I^k}}\succeq0.$$
--
--   The last implication holds independently of separability. This is the finite-copy stability that prevents strengthening this algebraic test by taking identical copies.
-- source:
--   Separability Criterion for Density Matrices, arXiv:quant-ph/9604005v2, Final paragraph, PDF p. 5. https://arxiv.org/abs/quant-ph/9604005v2 . PDF SHA-256: 6574d1af38e331a5ed4f7c58673855e1e580eb96d79fa52338f18cdc22d43998.

import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
import Definitions.Def_QAlgorithms_Defs_Hamiltonian
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P01_Model
set_option autoImplicit false

/-!
# Peres: Separability Criterion for Density Matrices

Source: arXiv:quant-ph/9604005v2, PDF pp.2–5. The first subsystem alone
is transposed, without complex conjugation. Equation (5), which has a
conjugating-factor defect, is deferred; its valid spectral conclusion is stated.
-/

noncomputable section

open scoped Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Independent1.P01

open QAlgorithms.Entanglement


















/-- Peres PDF p.5, final paragraph: finite identical copies preserve separability,
partial transposition commutes with the observer-grouped tensor product, and
nonnegative partial-transpose spectrum is preserved without separability. -/
theorem tensorPower_partialTranspose_stability
    {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
    [DecidableEq I] [DecidableEq J]
    (rho : Matrix (I × J) (I × J) ℂ) (density : IsDensityMatrix rho)
    (k : ℕ) (copies : 1 ≤ k) :
    (IsSeparableDensity rho → IsSeparableDensity (observerTensorPower rho k)) ∧
    partialTransposeFirst (observerTensorPower rho k) =
      observerTensorPower (partialTransposeFirst rho) k ∧
    ((partialTransposeFirst rho).PosSemidef →
      (partialTransposeFirst (observerTensorPower rho k)).PosSemidef) := by sorry

end QAlgorithms.Papers.Independent.Independent1.P01
