-- Prove2me | Theorems.Thm_QAlgorithms_pgmSuccess_uniform_real_gram
-- name    : QAlgorithms.pgmSuccess_uniform_real_gram
-- status  : Proved
-- author  : @fizzyinc3
-- created : 2026-10-17T08:57:39.824537+00:00
-- url     : https://prove2.me/theorems/e3628114-12f0-4834-8f5c-4092c71cf2e7
-- title:
--   Uniform PGM success from a real Gram matrix
-- statement:
--   Let $O$ and $I$ be finite sets, and let $\psi_i\in\mathbb C^I$ for each $i\in O$. Suppose the Gram matrix is real: a real matrix $G$ satisfies $G_{ij}=\langle\psi_i,\psi_j\rangle$ after inclusion into $\mathbb C$. Write $N=|O|$ and give every vector weight $1/N$. Then the pretty good measurement success quantity satisfies
--
--   $$
--   P^{\mathrm{PGM}}\bigl(\{(1/N,\psi_i)\}_{i\in O}\bigr)
--   =\frac1N\sum_{i\in O}\bigl(\sqrt G_{ii}\bigr)^2.
--   $$
--
--   Here $\sqrt G_{ii}$ denotes the $i$th diagonal entry of the positive semidefinite matrix square root of $G$. The inverse square root in the PGM definition is the spectral pseudoinverse, with value zero at the zero eigenvalue. This identity connects state identification to Gram matrix estimates and applies to the PAC and agnostic hard ensembles.
--
--   **Formalization Note** This is the uniform-prior, real-Gram specialization of the Gram identity in §7.3.2. The identity is homogeneous and therefore also applies to vectors without a unit-norm assumption. If $O$ is empty both sides are zero, with the convention $1/0=0$.
-- source:
--   Srinivasan Arunachalam, Quantum Algorithms and Learning Theory, 2018 thesis, ILLC DS-2018-08, §7.3.2, printed p.148 / PDF page159, displayed PGM Gram-matrix identity preceding Eq.(7.5); uniform-prior, real-Gram specialization. https://ir.cwi.nl/pub/27536/Thesis_S_Arunachalam

import Definitions.Def_QAlgorithms_Defs_BooleanFourier
set_option autoImplicit false
open scoped BigOperators

theorem QAlgorithms.pgmSuccess_uniform_real_gram {O ι : Type*}
    [Fintype O] [DecidableEq O] [Fintype ι] [DecidableEq ι]
    (ψ : O → EuclideanSpace ℂ ι) (G : Matrix O O ℝ)
    (hG : ∀ i j, inner ℂ (ψ i) (ψ j) = (G i j : ℂ)) :
    QAlgorithms.pgmSuccess (fun _ : O => (Fintype.card O : ℝ)⁻¹) ψ =
      (Fintype.card O : ℝ)⁻¹ * ∑ i, (QAlgorithms.psdSqrt G i i)^2 := by
  sorry
