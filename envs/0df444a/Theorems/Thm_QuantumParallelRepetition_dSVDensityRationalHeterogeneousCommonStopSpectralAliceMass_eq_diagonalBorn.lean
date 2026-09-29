-- Prove2me | Theorems.Thm_QuantumParallelRepetition_dSVDensityRationalHeterogeneousCommonStopSpectralAliceMass_eq_diagonalBorn
-- name    : QuantumParallelRepetition.dSVDensityRationalHeterogeneousCommonStopSpectralAliceMass_eq_diagonalBorn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T09:43:47.786482+00:00
-- url     : https://prove2.me/theorems/cd375a23-ccec-4cbb-bde1-1893b4fdf799
-- title:
--   The spectral Alice mass of the common-stop decomposition equals the diagonal Born success probability
-- statement:
--   Let $d,N\ge 1$, let $w$ be a width, and let $\xi,\zeta$ be bipartite unit vectors of local dimension $d$ with reduced densities $\rho_\xi,\rho_\zeta$. Write $c_{ij}=\mathrm{tr}\big(P_i^{\xi}P_j^{\zeta}\big)/(dN)$ for the normalized overlap of the $i$-th spectral projector of $\rho_\xi$ with the $j$-th spectral projector of $\rho_\zeta$, and let $r_w(\xi,i)\in\{0,\dots,N\}$ be the accepted rank of the $i$-th eigenvalue of $\rho_\xi$, i.e. the number of grid bins that accept it at width $w$. Then $$\sum_{i,j}c_{ij}\,r_w(\xi,i)=\frac1d\sum_{i}\frac{r_w(\xi,i)}{N},$$ and the right-hand side is precisely the diagonal Born success probability of the global POVM at width $w$ on the uniform threshold resource. So the $\zeta$-side of the spectral decomposition drops out of this particular weighted average.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L44816-L44876

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_23
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.SetLike.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Topology.Defs.Filter

open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

theorem
    QuantumParallelRepetition.dSVDensityRationalHeterogeneousCommonStopSpectralAliceMass_eq_diagonalBorn
    {d N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (w : ℝ) (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalHeterogeneousCommonStopSpectralAliceMass
        N w ξ ζ =
      dSVDensityRationalPhysicalDiagonalBornSuccess
        grid dimension w ξ := by sorry
