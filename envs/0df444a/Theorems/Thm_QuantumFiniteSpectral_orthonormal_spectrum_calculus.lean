-- Prove2me | Theorems.Thm_QuantumFiniteSpectral_orthonormal_spectrum_calculus
-- name    : QuantumFiniteSpectral.orthonormal_spectrum_calculus
-- status  : Proved
-- author  : @Mrnaiq
-- created : 2026-11-14T06:45:14.345766+00:00
-- url     : https://prove2.me/theorems/f0cc2e47-3935-4fef-bec7-26e1ba1672c0
-- title:
--   Complete orthonormal eigenvectors determine normality, positivity, and trace
-- statement:
--   Let $J$ be a complex matrix indexed by a finite set $I$. Suppose a family $(v_k)_{k\in K}$ is an orthonormal spanning family of $\mathbb C^I$ and consists of eigenvectors with arbitrary complex eigenvalues $e_k$. Then
--
--   $$J^\dagger J=JJ^\dagger,\qquad J\succeq0\iff(\forall k,\ e_k\ge0),\qquad\operatorname{Tr}J=\sum_ke_k.$$
--
--   The complex inequality $e_k\ge0$ includes that $e_k$ is real. The finite eigenvector index set may differ from the matrix index set; completeness supplies the required identification. Hermiticity is not assumed: normality follows, and real nonnegative eigenvalues are exactly the extra condition for positive semidefiniteness.
-- source:
--   Finite-dimensional spectral calculus underlying Mozrzymas, Studzinski and Datta, Structure of irreducibly covariant quantum channels for finite groups, https://arxiv.org/abs/1610.05657v2, PDF pp.15–16, Lemma 29, Proposition 30, Corollaries 33 and 35, and Remark 36 Eqs.(75)–(81); generalized from the complete Choi eigenbasis to arbitrary finite complex matrices.

import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ToLin
noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder
set_option backward.isDefEq.respectTransparency false

theorem QuantumFiniteSpectral.orthonormal_spectrum_calculus {I K : Type*} [Fintype I] [Fintype K] [DecidableEq I] [DecidableEq K] (J : Matrix I I ℂ) (v : K → I → ℂ) (e : K → ℂ)
    (horth : ∀ k l, (∑ i, conj (v k i) * v l i) = if k = l then 1 else 0)
    (hspan : Submodule.span ℂ (Set.range v) = ⊤)
    (heig : ∀ k, J.mulVec (v k) = e k • v k) :
    Jᴴ * J = J * Jᴴ ∧ (J.PosSemidef ↔ ∀ k, 0 ≤ e k) ∧ Matrix.trace J = ∑ k, e k := by sorry
