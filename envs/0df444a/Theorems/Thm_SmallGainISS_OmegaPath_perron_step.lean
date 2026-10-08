-- Prove2me | Theorems.Thm_SmallGainISS_OmegaPath_perron_step
-- name    : SmallGainISS.OmegaPath.perron_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:15:45.176966+00:00
-- url     : https://prove2.me/theorems/45052f5d-2a4a-4e58-aae5-845d1314474f
-- title:
--   §8.5, proof of Theorem 5.2 (i) — spectral radius $<1$ gives $v>0$ with $Gv<v$
-- statement:
--   Let $G$ be a real $n\times n$ matrix with nonnegative entries whose spectral radius is less than one, i.e. every complex eigenvalue $z$ of $G$ satisfies $|z|<1$. Then there exists a vector $v\in\mathbb R^n$ with $v_i>0$ for all $i$ and
--   $$(Gv)_i<v_i\qquad\text{for all } i .$$
--
--   For a linear gain operator $\Gamma_\mu=G$ this gives the $\Omega$-path $\sigma(r)=rv$, which is case (i) of Theorem 5.2.
-- source:
--   Dashkovskiy, Rüffer, Wirth, Small Gain Theorems for Large Scale Systems and Construction of ISS Lyapunov Functions, arXiv:0901.1842v2, p. 27, §8.5, proof of Theorem 5.2 (i)

import Mathlib
import Definitions.Def_SmallGainISS_OmegaPath_GainOperator

open scoped NNReal
open Filter Topology

namespace SmallGainISS.OmegaPath

/-- §8.5, proof of Theorem 5.2 (i) (p. 27): a real matrix `G` with nonnegative entries whose
complex eigenvalues all have modulus `< 1` admits a vector `v > 0` (every component positive)
with `G v < v` (strict componentwise). -/
theorem perron_step {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (hG : ∀ i j, 0 ≤ G i j)
    (hspec : ∀ z ∈ spectrum ℂ (G.map (algebraMap ℝ ℂ)), ‖z‖ < 1) :
    ∃ v : Fin n → ℝ, (∀ i, 0 < v i) ∧ ∀ i, G.mulVec v i < v i := by sorry

end SmallGainISS.OmegaPath
