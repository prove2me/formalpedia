-- Prove2me | Theorems.Thm_QAlgorithms_Arunachalam_vnEntropy_subadditive
-- name    : QAlgorithms.Arunachalam.vnEntropy_subadditive
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:55:20.618692+00:00
-- url     : https://prove2.me/theorems/4fb1211d-7466-4845-afaa-bb12db1e9676
-- title:
--   Subadditivity of von Neumann entropy
-- statement:
--   Let $\mathcal H_A$ and $\mathcal H_B$ be finite-dimensional Hilbert spaces and let $\rho_{AB}$ be a density matrix (positive semidefinite, trace one) on $\mathcal H_A\otimes\mathcal H_B$. Write $\rho_A=\operatorname{Tr}_B\rho_{AB}$ and $\rho_B=\operatorname{Tr}_A\rho_{AB}$ for its reduced states and $S(\rho)=-\operatorname{Tr}(\rho\log_2\rho)$ for the von Neumann entropy (with $0\log 0=0$). Then
--
--   $$
--   S(\rho_{AB})\le S(\rho_A)+S(\rho_B).
--   $$
--
--   This inequality is used to bound the mutual information between a concept and $T$ examples by $T$ times the information in one example.
--
--   **Formalization Note** $\rho\log_2\rho$ is computed by the continuous functional calculus applied to $x\mapsto x\log_2 x$; Lean's $\log 0=0$ gives the convention $0\log 0=0$.
-- source:
--   Srinivasan Arunachalam, Quantum Algorithms and Learning Theory — Part II, 2018 thesis, ILLC DS-2018-08, PDF p. 162, Fact 7.3.10. https://ir.cwi.nl/pub/27536/Thesis_S_Arunachalam

import Definitions.Def_QAlgorithms_Defs_Learning
set_option autoImplicit false

namespace QAlgorithms.Arunachalam

open QAlgorithms.Learning

/-- Arunachalam p.162, Fact 7.3.10 (subadditivity of quantum entropy): for every bipartite
density matrix `ρ_AB` on `H_A ⊗ H_B`, `S(ρ_AB) ≤ S(ρ_A) + S(ρ_B)`, where `S(ρ) = −Tr(ρ log ρ)`
(log base 2, §7.3.1) and `ρ_A = Tr_B ρ_AB`, `ρ_B = Tr_A ρ_AB` are the partial traces. -/
theorem vnEntropy_subadditive {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (ρ : Matrix (ι × κ) (ι × κ) ℂ) (hρ : IsDensityMatrix ρ) :
    vnEntropy ρ ≤ vnEntropy (traceRight ρ) + vnEntropy (traceLeft ρ) := by
  sorry






end QAlgorithms.Arunachalam
