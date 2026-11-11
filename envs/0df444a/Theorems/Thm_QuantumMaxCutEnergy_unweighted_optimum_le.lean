-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_unweighted_optimum_le
-- name    : QuantumMaxCutEnergy.unweighted_optimum_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T17:16:58.266056+00:00
-- url     : https://prove2.me/theorems/10e005d5-625c-4708-af3e-f95c099e8b3e
-- title:
--   $\lambda_{\max}(H_G)\le m+\lfloor n/2\rfloor$ for an unweighted graph
-- statement:
--   Let $G$ be a graph on $n$ vertices whose edge weights are all $0$ or $1$, with $m$ edges of weight $1$, and $H_G=\sum_{ij\in E}(I-\mathrm{SWAP}_{ij})$. Then
--
--   $$\lambda_{\max}(H_G)\le m+\lfloor n/2\rfloor .$$
--
--   It follows from the bound $m+\min(k,n-k)$ on the sector of Hamming weight $k$, where $H_G$ acts as the Laplacian of the token graph $F_k(G)$.
-- source:
--   Bakshi, Basu, Kothari and Li, arXiv:2605.14994v1, Theorem 3.1 (with b = -1), combined with the Hamming-weight block decomposition of Apte, Parekh and Sud, arXiv:2506.03441, Section 3.1, Fact 1.

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Mathlib
open scoped BigOperators

theorem QuantumMaxCutEnergy.unweighted_optimum_le {n : ℕ}
    (w : QuantumMaxCutEnergy.Weights n) (hw : ∀ e, w e = 0 ∨ w e = 1) :
    QuantumMaxCutEnergy.optimum ⟨n, w⟩ ≤ (∑ e, (w e : ℝ)) + ((n / 2 : ℕ) : ℝ) := by sorry
