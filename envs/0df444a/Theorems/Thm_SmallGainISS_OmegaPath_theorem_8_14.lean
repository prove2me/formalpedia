-- Prove2me | Theorems.Thm_SmallGainISS_OmegaPath_theorem_8_14
-- name    : SmallGainISS.OmegaPath.theorem_8_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:16:12.30659+00:00
-- url     : https://prove2.me/theorems/c20708b5-eac3-4bc4-be73-e66a2859445c
-- title:
--   Theorem 8.14 — for $\mu=\max$, if all subordinated cycles are contractions, an $\Omega$-path exists
-- statement:
--   Let $\Gamma=(\gamma_{ij})$ be a gain matrix with entries in $\mathcal K\cup\{0\}$ and $\gamma_{ii}\equiv0$, and let $\mu=\max$, so that
--   $$\Gamma_\mu(s)_i=\max_j\gamma_{ij}(s_j).$$
--   A cycle is a sequence of nonzero entries $(\gamma_{i_1i_2},\gamma_{i_2i_3},\dots,\gamma_{i_Ki_1})$; it is subordinated if $i_1>\max\{i_2,\dots,i_K\}$ and a contraction if $\gamma_{i_1i_2}\circ\gamma_{i_2i_3}\circ\dots\circ\gamma_{i_Ki_1}(r)<r$ for all $r>0$. If all subordinated cycles of $\Gamma$ are contractions, then there exists an $\Omega$-path with respect to $\Gamma_\mu$ (Definition 5.1).
--
--   This is case (iii) of Theorem 5.2 in its cycle-condition form; the paper gives only a sketch of the proof.
-- source:
--   Dashkovskiy, Rüffer, Wirth, Small Gain Theorems for Large Scale Systems and Construction of ISS Lyapunov Functions, arXiv:0901.1842v2, p. 27, Theorem 8.14

import Mathlib
import Definitions.Def_SmallGainISS_OmegaPath_GainOperator
import Definitions.Def_SmallGainISS_OmegaPath_IsOmegaPath

open scoped NNReal
open Filter Topology

namespace SmallGainISS.OmegaPath

/-- Theorem 8.14 (p. 27). Let `μ = max` and `Γ ∈ (𝒦 ∪ {0})ⁿˣⁿ` (with `γᵢᵢ ≡ 0`). If all subordinated
cycles of `Γ` are contractions, there exists an Ω-path with respect to `Γ_μ`. -/
theorem theorem_8_14 {n : ℕ} (Γ : SmallGainISS.Lyapunov.GainMatrix n)
    (hΓ : ∀ i j, SmallGainISS.Lyapunov.IsKOrZero (Γ i j)) (hdiag : SmallGainISS.Lyapunov.ZeroDiagonal Γ)
    (hcyc : SubordinatedCyclesContract Γ) :
    ∃ σ : ℝ≥0 → Fin n → ℝ≥0, IsOmegaPath (gainOp Γ maxAgg) σ := by sorry

end SmallGainISS.OmegaPath
