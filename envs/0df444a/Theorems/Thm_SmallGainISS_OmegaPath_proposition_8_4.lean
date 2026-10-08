-- Prove2me | Theorems.Thm_SmallGainISS_OmegaPath_proposition_8_4
-- name    : SmallGainISS.OmegaPath.proposition_8_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:16:22.129843+00:00
-- url     : https://prove2.me/theorems/ad9ad4b8-de34-4a3e-bc5c-c50f0f1c7833
-- title:
--   Proposition 8.4 — for bounded $\Gamma_\mu$ satisfying (SGC), an $\Omega$-path exists
-- statement:
--   Throughout, $n\ge 0$ is the number of subsystems, $\mathbb R_+=[0,\infty)$, and vectors in $\mathbb R^n_+$ are compared componentwise: $v\le w$ means $v_i\le w_i$ for all $i$, and $v<w$ means $v_i<w_i$ for **all** $i$. $\Gamma=(\gamma_{ij})$ is a gain matrix with $\gamma_{ii}\equiv0$, $\mu=(\mu_1,\dots,\mu_n)$ is a vector of monotone aggregation functions on $\mathbb R^n_+$ compatible with $\Gamma$ in the sense of Remark 2.6, and $\Gamma_\mu(s)_i=\mu_i(\gamma_{i1}(s_1),\dots,\gamma_{in}(s_n))$ is the gain operator.
--
--   Assume all gains are in $\mathcal K\cup\{0\}$, $\Gamma$ has no zero rows, $\Gamma_\mu$ satisfies the small gain condition $\Gamma_\mu\not\ge\mathrm{id}$, and $\Gamma_\mu$ is bounded, i.e. the set $\Gamma_\mu(\mathbb R^n_+)$ is bounded. Then there exists an $\Omega$-path $\sigma$ with respect to $\Gamma_\mu$:
--   $$\Gamma_\mu(\sigma(r))<\sigma(r)\qquad\text{for all } r>0,$$
--   together with the regularity (i)–(ii) of Definition 5.1.
--
--   This is case (iv) of Theorem 5.2 under the additional no-zero-rows hypothesis of the proposition.
-- source:
--   Dashkovskiy, Rüffer, Wirth, Small Gain Theorems for Large Scale Systems and Construction of ISS Lyapunov Functions, arXiv:0901.1842v2, p. 22, Proposition 8.4

import Mathlib
import Definitions.Def_SmallGainISS_OmegaPath_GainOperator
import Definitions.Def_SmallGainISS_OmegaPath_IsOmegaPath

open scoped NNReal
open Filter Topology

namespace SmallGainISS.OmegaPath

/-- Proposition 8.4 (p. 22). If `Γ` has no zero rows, `Γ_μ` satisfies (SGC) and `Γ_μ` is bounded,
then there exists an Ω-path with respect to `Γ_μ`. -/
theorem proposition_8_4 {n : ℕ} (Γ : SmallGainISS.Lyapunov.GainMatrix n) (μ : Fin n → (Fin n → ℝ≥0) → ℝ≥0)
    (hΓ : ∀ i j, SmallGainISS.Lyapunov.IsKOrZero (Γ i j)) (hdiag : SmallGainISS.Lyapunov.ZeroDiagonal Γ) (hrows : NoZeroRows Γ)
    (hμ : ∀ i, SmallGainISS.Lyapunov.IsMAF (μ i)) (hcomp : Compatible Γ μ) (hsgc : SGC (gainOp Γ μ))
    (hbdd : IsBoundedOp (gainOp Γ μ)) :
    ∃ σ : ℝ≥0 → Fin n → ℝ≥0, IsOmegaPath (gainOp Γ μ) σ := by sorry

end SmallGainISS.OmegaPath
