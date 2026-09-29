-- Prove2me | Theorems.Thm_RHLinalg_normSqMatrix_mem_doublyStochastic_of_unitary
-- name    : RHLinalg.normSqMatrix_mem_doublyStochastic_of_unitary
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:38:21.003315+00:00
-- url     : https://prove2.me/theorems/37cb34d4-4eba-4c70-839e-fb27e9128ad5
-- title:
--   The entrywise squared-norm matrix of a unitary is doubly stochastic
-- statement:
--   For an $n \times n$ matrix $W$ over an `RCLike` field $\mathbb{K}$, let $\operatorname{normSqMatrix}(W)$ be the real matrix with entries $\|W_{ij}\|^2$.
--
--   **Statement.** If $W$ is unitary ($W \in U(n, \mathbb{K})$), then
--   $$\bigl( \|W_{ij}\|^2 \bigr)_{i,j} \;\in\; \text{doublyStochastic}(\mathbb{R}, n),$$
--   i.e. all entries are nonnegative and every row and every column sums to $1$ (the rows and columns of a unitary matrix are unit vectors).
--
--   This standard observation supplies the doubly stochastic matrix to which the rearrangement step `RHLinalg.bilinear_doublyStochastic_le_of_monovary` is applied in the proof of von Neumann's trace inequality `RHLinalg.vonNeumann_trace_ineq`, in the module `Zeta23.LinAlg.VonNeumann` of the project's linear-algebra layer.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/LinAlg/VonNeumann.lean#L58-L74

import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Matrix.PosDef
import Definitions.Def_Zeta23_LinAlg_PosIndex
import Definitions.Def_Zeta23_LinAlg_VonNeumann

open Matrix Finset
open scoped ComplexOrder
open RHLinalg
variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem RHLinalg.normSqMatrix_mem_doublyStochastic_of_unitary
    {W : Matrix n n 𝕜} (hW : W ∈ Matrix.unitaryGroup n 𝕜) :
    normSqMatrix W ∈ doublyStochastic ℝ n := by sorry
