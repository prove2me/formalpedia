-- Prove2me | Theorems.Thm_TensorNP_Eigen_theorem_1_3
-- name    : TensorNP.Eigen.theorem_1_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:08:16.553822+00:00
-- url     : https://prove2.me/theorems/743339ae-90ed-48db-9ff7-8dbf34e4b6f7
-- title:
--   Theorem 1.3 — graph 3-colorability reduces to tensor $0$-eigenvalue over $\mathbb R$
-- statement:
--   Graph 3-colorability is polynomial-time many-one reducible to tensor $0$-eigenvalue over $\mathbb R$: there is a function $f$, computable by a Turing machine in time polynomial in the length of its input, such that for every binary string $w$,
--
--   $$w\in\textsf{3-COL}\iff f(w)\in\textsf{TENSOR-0-EIG}_{\mathbb R}.$$
--
--   Here $\textsf{3-COL}$ is the set of binary codes of simple graphs having a proper 3-coloring, and $\textsf{TENSOR-0-EIG}_{\mathbb R}$ is the set of binary codes of rational tensors $\mathcal A=[\![a_{ijk}]\!]\in\mathbb Q^{n\times n\times n}$ (any $n$) for which there is $\mathbf 0\ne\mathbf x\in\mathbb R^n$ with
--
--   $$\sum_{i,j=1}^{n}a_{ijk}x_ix_j=0,\qquad k=1,\dots,n,$$
--
--   that is, for which $\lambda=0$ is an eigenvalue with a real eigenvector (Problem 1.2 with $F=\mathbb R$, $\lambda=0$).
--
--   Since graph 3-colorability is NP-complete (Karp 1972, cited by the paper and not formalized here), deciding tensor eigenvalue over $\mathbb R$ is NP-hard.
--
--   **Formalization Note** "Polynomially reducible" is stated as Cook's polynomial-time many-one reducibility (`CookPvsNP.PolyReducible`): the paper's reduction maps one graph to one tensor, and a many-one reduction implies the oracle notion of the paper's §1.4. Instances are coded in binary as fixed in the definition file (rationals as numerator and denominator); the reduction produces integer tensors, which are rationals with denominator 1. NP-completeness of 3-colorability is not part of the statement.
-- source:
--   Hillar & Lim, Most Tensor Problems Are NP-Hard, J. ACM 60(6) (2013), Art. 45 (final version, arXiv:0911.1393v5), p. 0:7, Theorem 1.3 (proof p. 0:20)

import Mathlib
import Definitions.Def_TensorNP_Eigen_Defs

namespace TensorNP.Eigen

open CookPvsNP

/-- Theorem 1.3: graph 3-colorability is polynomial-time many-one reducible to tensor
`0`-eigenvalue over `ℝ` (Problem 1.2 with `F = ℝ`, `λ = 0`, rational tensors). -/
theorem theorem_1_3 : PolyReducible threeColLang tensorZeroEigLangR := by sorry

end TensorNP.Eigen
