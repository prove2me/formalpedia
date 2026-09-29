-- Prove2me | Theorems.Thm_RHLinalg_posIndex_add_le
-- name    : RHLinalg.posIndex_add_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:38:31.959326+00:00
-- url     : https://prove2.me/theorems/f51cc156-d543-48a3-8eca-c9269cb1fbfd
-- title:
--   Subadditivity of the positive index: $n_+(Q_1 + Q_2) \le n_+(Q_1) + n_+(Q_2)$
-- statement:
--   For a Hermitian matrix $Q$ over an `RCLike` field, let $n_+(Q)$ (`posIndex`) be the number of strictly positive eigenvalues — equivalently, by Sylvester's law of inertia, the maximal dimension of a subspace on which the form $x \mapsto x^{\mathsf H} Q x$ is positive definite.
--
--   **Statement.** For Hermitian $m \times m$ matrices $Q_1, Q_2$,
--   $$n_+(Q_1 + Q_2) \;\le\; n_+(Q_1) + n_+(Q_2).$$
--
--   The proof runs through the subspace characterization: a subspace on which $Q_1 + Q_2$ is positive definite meets the intersection of suitable complements, splitting its dimension between contributions counted by $n_+(Q_1)$ and $n_+(Q_2)$. This is the subadditivity statement appearing in Section 3 of the paper, just after the inertia lemma (`lem:inertia`).
--
--   In the module `Zeta23.LinAlg.Inertia` it is consumed by the zero-side block estimates `Zeta23.ZeroSide.ZeroBlockData.posIndex_blockA_le` and `posIndex_blockQ_le`, which control the number of positive eigenvalues of the block matrices arising in the matrix-variational argument for Theorem A.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/LinAlg/Inertia.lean#L88-L136, docstring tag [lem:inertia]

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Definitions.Def_Zeta23_LinAlg_PosIndex

open Matrix Finset Submodule
open scoped ComplexOrder
open RHLinalg
variable {𝕜 : Type*} [RCLike 𝕜]
variable {m d : Type*} [Fintype m] [DecidableEq m] [Fintype d] [DecidableEq d]

theorem RHLinalg.posIndex_add_le {Q₁ Q₂ : Matrix m m 𝕜}
    (hQ₁ : Q₁.IsHermitian) (hQ₂ : Q₂.IsHermitian) :
    posIndex (hQ₁.add hQ₂) ≤ posIndex hQ₁ + posIndex hQ₂ := by sorry
