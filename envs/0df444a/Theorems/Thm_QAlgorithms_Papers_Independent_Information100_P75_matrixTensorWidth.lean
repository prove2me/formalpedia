-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P75_matrixTensorWidth
-- name    : QAlgorithms.Papers.Independent.Information100.P75.matrixTensorWidth
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T13:15:12.706187+00:00
-- url     : https://prove2.me/theorems/b795f8a7-9b0b-4629-a69d-bba74697e914
-- title:
--   Saturated additivity for two matrices
-- statement:
--   For a square complex matrix $X$, $W(X)$ denotes its numerical range, equivalently the values $\operatorname{Tr}(\sigma X)$ over PSD matrices $\sigma$ of trace one. Put $\Gamma_X=\{\theta\in[-\pi,\pi):\operatorname{Re}(e^{i\theta}X)\succeq0\}$, where $\operatorname{Re}Y=(Y+Y^\dagger)/2$, with Lebesgue length $|\Gamma_X|$ in radians. The ordinary width is $\operatorname{sw}(X)=\pi$ when $0\in W(X)$ and $\pi-|\Gamma_X|$ otherwise. For a complex subspace $\mathcal M$, $\operatorname{sw}^*(\mathcal M)=\inf_{X\in\mathcal M}\operatorname{sw}(X)$. The overlined width of a nonzero matrix is $\overline{\operatorname{sw}}(X)=\pi-|\Gamma_X|$.
--
--   For any $n,m\ge1$ and matrices $A\in M_n(\mathbb C)$ and $B\in M_m(\mathbb C)$,
--
--   $$\operatorname{sw}(A\otimes B)=\min\{\operatorname{sw}(A)+\operatorname{sw}(B),\pi\}.$$
--
--   The widths here are ordinary widths. The identity includes zero and singular factors and supplies the individual-matrix tensor rule.
-- source:
--   Parallel quantum channel discrimination and numerical ranges in tensor product subspaces, arXiv:2609.20781v1, PDF p. 8, Lemma 14

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P75

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P75

open Classical

open scoped ComplexConjugate ComplexOrder Matrix

open MeasureTheory

/-- Lemma 14, PDF p.8: saturated additivity of ordinary matrix widths, including
zero factors and singular matrices. -/
theorem matrixTensorWidth {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype κ] [DecidableEq κ] [Nonempty κ] (X : Mat ι) (Y : Mat κ) :
    width (Matrix.kronecker X Y) = min (width X + width Y) Real.pi := by sorry

end QAlgorithms.Papers.Independent.Information100.P75

end
