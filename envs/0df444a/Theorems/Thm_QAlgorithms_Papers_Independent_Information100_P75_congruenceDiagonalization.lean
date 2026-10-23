-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P75_congruenceDiagonalization
-- name    : QAlgorithms.Papers.Independent.Information100.P75.congruenceDiagonalization
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T13:11:55.100405+00:00
-- url     : https://prove2.me/theorems/6bf03743-50f0-4a1a-b79a-70ebc2c762f3
-- title:
--   Congruence diagonalization under an overlined-width bound
-- statement:
--   For a square complex matrix $X$, $W(X)$ denotes its numerical range, equivalently the values $\operatorname{Tr}(\sigma X)$ over PSD matrices $\sigma$ of trace one. Put $\Gamma_X=\{\theta\in[-\pi,\pi):\operatorname{Re}(e^{i\theta}X)\succeq0\}$, where $\operatorname{Re}Y=(Y+Y^\dagger)/2$, with Lebesgue length $|\Gamma_X|$ in radians. The ordinary width is $\operatorname{sw}(X)=\pi$ when $0\in W(X)$ and $\pi-|\Gamma_X|$ otherwise. For a complex subspace $\mathcal M$, $\operatorname{sw}^*(\mathcal M)=\inf_{X\in\mathcal M}\operatorname{sw}(X)$. The overlined width of a nonzero matrix is $\overline{\operatorname{sw}}(X)=\pi-|\Gamma_X|$.
--
--   Let $n\ge1$ and $0\ne A\in M_n(\mathbb C)$ satisfy $\overline{\operatorname{sw}}(A)<\pi$. Then there exist a nonsingular $G\in M_n(\mathbb C)$ and complex scalars $v_1,\ldots,v_n$ such that
--
--   $$A=G\operatorname{diag}(v_1,\ldots,v_n)G^\dagger,\qquad |v_j|\in\{0,1\}\quad(1\le j\le n).$$
--
--   This includes singular matrices through the allowed zero diagonal entries.
-- source:
--   Parallel quantum channel discrimination and numerical ranges in tensor product subspaces, arXiv:2609.20781v1, PDF p. 7, Lemma 10

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P75

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P75

open Classical

open scoped ComplexConjugate ComplexOrder Matrix

open MeasureTheory

/-- Lemma 10, PDF p.7: congruence factorization from overlined width. Singular
matrices are allowed: diagonal entries may have modulus zero as well as one. -/
theorem congruenceDiagonalization {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (X : Mat ι) (hX : X ≠ 0) (hw : closedWidth X < Real.pi) :
    ∃ (G : Mat ι) (v : ι → ℂ), IsUnit G.det ∧ X = G * Matrix.diagonal v * Gᴴ ∧
      ∀ j, ‖v j‖ = 0 ∨ ‖v j‖ = 1 := by sorry

end QAlgorithms.Papers.Independent.Information100.P75

end
