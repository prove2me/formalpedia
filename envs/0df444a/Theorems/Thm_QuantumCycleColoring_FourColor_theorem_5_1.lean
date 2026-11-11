-- Prove2me | Theorems.Thm_QuantumCycleColoring_FourColor_theorem_5_1
-- name    : QuantumCycleColoring.FourColor.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T18:00:05.506109+00:00
-- url     : https://prove2.me/theorems/56ed521e-b69d-4de4-b3df-584af9a1f38f
-- title:
--   Theorem 5.1: zero energy and maximal mass force a balanced $\Lambda$-invariant cut space
-- statement:
--   Let $P$ be a PSD operator on $\mathbb C^N\otimes\mathbb C^N$ with $0\preceq P\preceq I$, and $\Lambda$ a PSD $N\times N$ matrix with $\|\Lambda\|_F=1$ and $\Lambda\succ0$. If
--   $$m_\Lambda(P)=\tfrac14\quad\text{and}\quad\mathcal E_\Lambda(P)=0,$$
--   then there is an orthogonal decomposition $\mathbb C^N=U\oplus U^\perp$ such that
--
--   1. (P1) $P=\Pi_{L(U^\perp,U)}$, the orthogonal projector onto (the vectorization of) the cut space $L(U^\perp,U)=\mathrm{span}\{xy^\dagger:x\in U,\ y\in U^\perp\}$;
--   2. (P2) $\mathrm{Tr}(\Lambda^2\Pi_U)=\mathrm{Tr}(\Lambda^2\Pi_{U^\perp})=\tfrac12$;
--   3. (P3) $U$ and $U^\perp$ are $\Lambda$-invariant: $\Lambda U=U$ and $\Lambda U^\perp=U^\perp$.
--
--   This is the exact structure theorem behind the reduction from four to three colours: an outcome with maximal mass and no collisions is a complete balanced cut, aligned with the eigenspaces of $\Lambda$.
--
--   Differences from the source:
--   - encoding: Λ-mass m_Λ(P) = Tr(P(Λ²⊗Λ̄²)) and Λ-energy E_Λ(P) = Tr(ΛAΛB), complex traces that are real for PSD P, Λ → mass Λ P and energy Λ P are the real parts of these traces; reason: the traces are real for PSD P and Λ, so the values are the same
--   - encoding: ℂ^N with its standard basis, operators on ℂ^N ⊗ ℂ^N → vectors indexed by an arbitrary finite type d (N = card d), operators are matrices indexed by d × d with the Kronecker product for ⊗; reason: relabelling the standard basis; the same instances
--   - encoding: P = Π_{L(U⊥,U)}, the projector onto the matrix space L(U⊥,U) ⊆ ℂ^{N×N} ≅ ℂ^N ⊗ ℂ^N → P = projMat (cutSpace U), the orthogonal projector onto span{vec(x y†) : x ∈ U, y ∈ U⊥} in EuclideanSpace ℂ (d × d); reason: the paper's identification of matrices with bipartite vectors by vec; the literal span form
--   - encoding: an orthogonal decomposition ℂ^N = U ⊕ U⊥; ΛU = U, ΛU⊥ = U⊥ → a subspace U of EuclideanSpace ℂ d with its orthogonal complement Uᗮ; the images of U and Uᗮ under the linear map of Λ equal U and Uᗮ; reason: the same decompositions and the same invariance
--   - encoding: PSD Λ with ‖Λ‖_F = 1 and Λ ≻ 0 → Λ.PosDef and frobNorm Λ = 1; reason: positive definiteness includes positive semidefiniteness, so the PSD hypothesis is implied
-- source:
--   Tom Gur, Longcheng Li, STOC 2027 submission #515 (October 2026), Theorem 5.1, p.25

import Mathlib
import Definitions.Def_FuchsVdGraaf_IsPOVM
import Definitions.Def_QuantumCycleColoring_FourColor_MatrixAnalysis

open scoped Kronecker ComplexOrder

namespace QuantumCycleColoring.FourColor

open Matrix

/-- Theorem 5.1, p.25 (Gur–Li, STOC 2027 #515). For PSD `P` with `0 ⪯ P ⪯ I` and PSD
`Λ` with `‖Λ‖_F = 1` and `Λ ≻ 0`, if `m_Λ(P) = 1/4` and `E_Λ(P) = 0`, there is a subspace `U`
(so `ℂ^d = U ⊕ U^⊥`) with
(P1) `P = Π_{L(U^⊥,U)}`, the orthogonal projector onto `vec(span{x y† : x ∈ U, y ∈ U^⊥})`;
(P2) `Tr(Λ² Π_U) = Tr(Λ² Π_{U^⊥}) = 1/2`;
(P3) `Λ U = U` and `Λ U^⊥ = U^⊥`. -/
theorem theorem_5_1 {d : Type} [Fintype d] [DecidableEq d]
    (P : Matrix (d × d) (d × d) ℂ) (hP : P.PosSemidef) (hPI : (1 - P).PosSemidef)
    (Λ : Matrix d d ℂ) (hΛF : frobNorm Λ = 1) (hΛpos : Λ.PosDef)
    (hm : mass Λ P = 1 / 4) (hE : energy Λ P = 0) :
    ∃ U : Submodule ℂ (EuclideanSpace ℂ d),
      P = projMat (cutSpace U) ∧
      (Matrix.trace (Λ * Λ * projMat U) = 1 / 2 ∧ Matrix.trace (Λ * Λ * projMat Uᗮ) = 1 / 2) ∧
      (U.map (Matrix.toEuclideanLin Λ) = U ∧ Uᗮ.map (Matrix.toEuclideanLin Λ) = Uᗮ) := by sorry

end QuantumCycleColoring.FourColor
