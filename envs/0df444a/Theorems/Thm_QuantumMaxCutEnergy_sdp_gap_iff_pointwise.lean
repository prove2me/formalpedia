-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_sdp_gap_iff_pointwise
-- name    : QuantumMaxCutEnergy.sdp_gap_iff_pointwise
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-01T16:54:42.673348+00:00
-- url     : https://prove2.me/theorems/fe530d38-cf61-493d-ab46-77c44b5fadee
-- title:
--   Pointwise form of a semidefinite relaxation bound
-- statement:
--   Let $A$ be a symmetric weight matrix, let $S$ be the value of the standard semidefinite Max-Cut relaxation of $A$, let $C>0$ and let $M$ be any real number. Then
--
--   $$C\,S \le M$$
--
--   holds if and only if every feasible relaxation matrix $X$ (symmetric positive semidefinite with unit diagonal) satisfies $C\cdot \tfrac14\sum_{i,j} A_{ij}(1-X_{ij}) \le M$.
--
--   The right-hand side is the pointwise elimination of the supremum that defines the relaxation value: because $S$ is the *least* upper bound of the relaxation objectives, it is enough (and necessary) that the scaled objective of every single feasible $X$ be at most $M$. This is the reduction step that turns a target of the form $0.954\,S\le \mathrm{OPT}$ into the state-construction statement "for every feasible $X$ there is a state whose energy is at least $0.954$ times the objective of $X$". No analysis, rounding or probability is involved; the content is order theory.
-- source:
--   Order-theoretic support lemma for Anshu-Gosset-Morenz TQC 2020 Theorem 1 / Lemma 2.1 of Briet-de Oliveira Filho-Vallentin, Theory of Computing 10(4) 2014, https://doi.org/10.4086/toc.2014.v010a004 , used to reduce the campaign leaf 0.954*S <= OPT to a pointwise rank-three rounding statement.

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations
import Mathlib
open scoped BigOperators

theorem QuantumMaxCutEnergy.sdp_gap_iff_pointwise
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (S C M : ℝ) (hC : 0 < C)
    (hS : ModernConvex.Relaxations.IsMaxcutSDPValue A S) :
    C * S ≤ M ↔ ∀ X : Matrix (Fin n) (Fin n) ℝ, ModernConvex.Relaxations.IsUnitDiagPSD X →
      C * ModernConvex.Relaxations.maxcutRelaxationObjective A X ≤ M := by sorry
