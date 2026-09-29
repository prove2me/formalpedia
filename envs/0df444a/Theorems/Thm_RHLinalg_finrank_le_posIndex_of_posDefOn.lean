-- Prove2me | Theorems.Thm_RHLinalg_finrank_le_posIndex_of_posDefOn
-- name    : RHLinalg.finrank_le_posIndex_of_posDefOn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:38:14.283877+00:00
-- url     : https://prove2.me/theorems/dedae91d-f2bc-4d8b-a0c3-dbbe1cca7bba
-- title:
--   Sylvester's inequality (hard direction): $\dim W \le n_+(A)$ for subspaces where $A$ is positive definite
-- statement:
--   Let $A$ be an $n \times n$ Hermitian matrix over $\mathbb{K}$ ($\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, an `RCLike` field), and let $n_+(A)$ (`posIndex`) denote its *positive index*: the number of strictly positive eigenvalues. Let $W \subseteq \mathbb{K}^n$ be a subspace on which the Hermitian form is positive definite, i.e. $\operatorname{Re}(x^{\mathsf H} A x) > 0$ for every nonzero $x \in W$ (`PosDefOn`).
--
--   **Statement.**
--   $$\dim_{\mathbb{K}} W \;\le\; n_+(A).$$
--
--   This is the hard direction of the subspace characterization of the positive index from Sylvester's law of inertia: no subspace on which the form is positive definite can exceed the number of positive eigenvalues. Together with the easy direction `RHLinalg.posDefOn_range_hermPosPart` (the form is positive definite on a subspace of dimension exactly $n_+(A)$), it makes the inertia lemma of the paper (docstring reference `lem:inertia`) immediate. In the module `Zeta23.LinAlg.Sylvester` it is consumed by `Zeta23.ZeroSide.posIndex_smul_pos` in the zero-side positivity analysis of the matrix-variational argument.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/LinAlg/Sylvester.lean#L77-L113, docstring tag [lem:inertia]

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Definitions.Def_Zeta23_LinAlg_HermitianPosPart
import Definitions.Def_Zeta23_LinAlg_PosIndex
import Definitions.Def_Zeta23_LinAlg_Sylvester

open Matrix Finset Submodule
open scoped ComplexOrder
open RHLinalg
variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem RHLinalg.finrank_le_posIndex_of_posDefOn {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {W : Submodule 𝕜 (n → 𝕜)} (hW : PosDefOn A W) :
    Module.finrank 𝕜 W ≤ posIndex hA := by sorry
