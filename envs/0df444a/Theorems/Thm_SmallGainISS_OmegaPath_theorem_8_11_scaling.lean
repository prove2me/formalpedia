-- Prove2me | Theorems.Thm_SmallGainISS_OmegaPath_theorem_8_11_scaling
-- name    : SmallGainISS.OmegaPath.theorem_8_11_scaling
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:15:38.8929+00:00
-- url     : https://prove2.me/theorems/567ab09c-765c-40ee-8d7f-803038691b4a
-- title:
--   §8.2, proof of Theorem 8.11 — strict increase of $\Gamma_\mu$ and a scaling $\varphi>\mathrm{id}$ with $\Gamma_\mu\circ\mathrm{diag}(\varphi)\not\ge\mathrm{id}$
-- statement:
--   Throughout, $n\ge 0$ is the number of subsystems, $\mathbb R_+=[0,\infty)$, and vectors in $\mathbb R^n_+$ are compared componentwise: $v\le w$ means $v_i\le w_i$ for all $i$, and $v<w$ means $v_i<w_i$ for **all** $i$. $\Gamma=(\gamma_{ij})$ is a gain matrix with $\gamma_{ii}\equiv0$, $\mu=(\mu_1,\dots,\mu_n)$ is a vector of monotone aggregation functions on $\mathbb R^n_+$ compatible with $\Gamma$ in the sense of Remark 2.6, and $\Gamma_\mu(s)_i=\mu_i(\gamma_{i1}(s_1),\dots,\gamma_{in}(s_n))$ is the gain operator.
--
--   Assume all gains are in $\mathcal K_\infty\cup\{0\}$, $\Gamma$ is irreducible and $\Gamma_\mu\not\ge\mathrm{id}$. Then
--
--   1. $\Gamma_\mu(v)<\Gamma_\mu(w)$ whenever $v<w$ (strict in every component);
--   2. there is $\varphi\in\mathcal K_\infty$ with $\varphi(r)>r$ for all $r>0$ such that, for $D=\mathrm{diag}(\varphi)$,
--   $$\Gamma_\mu\circ D\not\ge\mathrm{id}.$$
--
--   This is the first step of the proof of Theorem 8.11 (p. 24); part 2 is quoted there from [25, Prop. 5.8] and is stated here with the hypotheses as the paper uses it, without the subadditivity (M4) that [25] assumes for aggregation functions.
-- source:
--   Dashkovskiy, Rüffer, Wirth, Small Gain Theorems for Large Scale Systems and Construction of ISS Lyapunov Functions, arXiv:0901.1842v2, p. 24, §8.2, proof of Theorem 8.11 (citing [25, Prop. 5.8])

import Mathlib
import Definitions.Def_SmallGainISS_OmegaPath_GainOperator

open scoped NNReal
open Filter Topology

namespace SmallGainISS.OmegaPath

/-- The step of the proof of Theorem 8.11 cited from [25, Prop. 5.8] (§8.2, p. 24), with the
hypotheses as used there: for `Γ ∈ (𝒦∞ ∪ {0})ⁿˣⁿ` irreducible, `μ ∈ MAFⁿₙ` and `Γ_μ ≱ id`,
(a) `Γ_μ(v) < Γ_μ(w)` whenever `v < w`, and (b) there is `φ ∈ 𝒦∞`, `φ > id`, with
`Γ_μ ∘ diag(φ) ≱ id`. -/
theorem theorem_8_11_scaling {n : ℕ} (Γ : SmallGainISS.Lyapunov.GainMatrix n) (μ : Fin n → (Fin n → ℝ≥0) → ℝ≥0)
    (hΓ : ∀ i j, SmallGainISS.Lyapunov.IsKInfOrZero (Γ i j)) (hdiag : SmallGainISS.Lyapunov.ZeroDiagonal Γ) (hμ : ∀ i, SmallGainISS.Lyapunov.IsMAF (μ i))
    (hcomp : Compatible Γ μ) (hirr : IsIrreducible Γ) (hsgc : SGC (gainOp Γ μ)) :
    StrictlyIncreasingOp (gainOp Γ μ) ∧
    ∃ φ : ℝ≥0 → ℝ≥0, SmallGainISS.Lyapunov.IsKInf φ ∧ GtId φ ∧ SGC (gainOp Γ μ ∘ diagOp φ) := by sorry

end SmallGainISS.OmegaPath
