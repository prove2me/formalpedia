-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P47_k_extension_test
-- name    : QAlgorithms.Papers.Independent.Extend50.P47.k_extension_test
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:22:45.131365+00:00
-- url     : https://prove2.me/theorems/9e786d80-acb5-4704-a300-0af6a7884649
-- title:
--   Bipartite k-extendibility test, (96)
-- statement:
--   Every register has a fixed finite nonempty computational basis. States are positive semidefinite trace-one matrices, and pure vectors have norm one. Write $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1^2$ for squared fidelity. Here $G$ is a finite group and $U$ denotes its specified unitary representation. Raw Bose averages $\Pi=|G|^{-1}\sum_gU(g)$ use an ordinary representation; conjugation symmetry permits a projective representation. The set $\mathrm{Sym}_G$ consists of invariant densities; $\mathrm{B\!\text{-}Sym}_G$ consists of densities supported by $\Pi$. The sets $\mathrm{SymExt}_G$ and $\mathrm{BSE}_G$ are their normalized-extension marginal analogues, tracing out precisely the stated reference register. The input includes a unit purification of $\rho_S$. The prover acts only on its purifying register, with arbitrary ancillas and a retained private environment, and returns the prescribed registers. It never acts on retained $S$. All maxima mentioned below are attained.
--
--   For k≥1 with the same S,R and literal permutation representation, Algorithm 4 has optimum max squared fidelity over ordinary k-extendible states.
--
--   $$
--   p_4^{\rm opt}=\max_{\sigma\in k\text{-E}}F(\rho_{AB},\sigma).
--   $$
--
--   The formula gives the exact characterization or operational specialization described in the cited result.
-- source:
--   Testing symmetry on quantum computers, arXiv:2105.12758v3, PDF p. 14, Bipartite k-extendibility test, (96)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P47

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P47

open scoped ComplexConjugate ComplexOrder Matrix Matrix.Norms.L2Operator Manifold ContDiff

open MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Information100.P56 (normalizedChoi)

variable {G S R P T A B C D R2 S2 : Type*}

variable [Fintype G] [Group G] [DecidableEq G]

variable [Fintype S] [DecidableEq S] [Nonempty S]

variable [Fintype R] [DecidableEq R] [Nonempty R]

variable [Fintype P] [DecidableEq P] [Nonempty P]

variable [Fintype T] [DecidableEq T] [Nonempty T]

variable [Fintype A] [DecidableEq A] [Nonempty A]

variable [Fintype B] [DecidableEq B] [Nonempty B]

variable [Fintype C] [DecidableEq C] [Nonempty C]

variable [Fintype D] [DecidableEq D] [Nonempty D]

variable [Fintype R2] [DecidableEq R2] [Nonempty R2]

variable [Fintype S2] [DecidableEq S2] [Nonempty S2]

/-- PDF pp.14–15, (96): ordinary k-extendibility tests; k=1 imposes no constraint. -/
theorem k_extension_test [Nonempty P] [Nonempty A] [Nonempty B] (n : ℕ) (rho : Mat (A × B)) (hrho : IsDensityMatrix rho)
    (psi : EuclideanSpace ℂ (P × (A × B))) (hpsi : ‖psi‖ = 1)
    (hpur : traceLeft (pureDensity psi) = rho) :
    TestIdentity psi (seTest (kFamily (A := A) (B := B) n)) rho
      (SE (kFamily (A := A) (B := B) n)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P47

end
