-- Prove2me | Theorems.Thm_SmallGainISS_OmegaPath_lemma_8_6
-- name    : SmallGainISS.OmegaPath.lemma_8_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:15:31.577204+00:00
-- url     : https://prove2.me/theorems/80e68097-d9ab-4400-ab87-7edd623cf3b5
-- title:
--   Lemma 8.6 — factorizations $D=D_1^{(k)}\circ D_2^{(k)}$ of diagonal operators
-- statement:
--   Fix $n$ and write $\mathrm{diag}(\rho)(s)_i=\rho(s_i)$ for $s\in\mathbb R^n_+$.
--
--   1. Let $D=\mathrm{diag}(\rho)$ with $\rho\in\mathcal K_\infty$ and $\rho>\mathrm{id}$. Then there are $\rho_1^{(k)},\rho_2^{(k)}\in\mathcal K_\infty$, $k\ge0$, with $\rho_i^{(k)}>\mathrm{id}$, such that for $D_i^{(k)}=\mathrm{diag}(\rho_i^{(k)})$
--   $$D=D_1^{(k)}\circ D_2^{(k)}\qquad\text{for every }k\ge0,$$
--   and the family can be chosen so that $D_2^{(k)}(s)<D_2^{(k+1)}(s)$ for all $k\ge0$ and all $s>0$.
--   2. Let $D=\mathrm{diag}(\mathrm{id}+\alpha)$ with $\alpha\in\mathcal K_\infty$. Then there are $\alpha_1,\alpha_2\in\mathcal K_\infty$ with $D=\mathrm{diag}(\mathrm{id}+\alpha_1)\circ\mathrm{diag}(\mathrm{id}+\alpha_2)$.
--
--   Here $\rho>\mathrm{id}$ means $\rho(r)>r$ for all $r>0$, and $<$ between vectors is strict in every component. The factorizations provide the "extra space" used in the proof of Theorem 8.11 to make a monotone sequence strictly increasing.
--
--   **Formalization Note** In part 1 the whole family $(\rho_1^{(k)},\rho_2^{(k)})_{k\ge0}$ is chosen once, before the monotonicity in $k$ is required.
-- source:
--   Dashkovskiy, Rüffer, Wirth, Small Gain Theorems for Large Scale Systems and Construction of ISS Lyapunov Functions, arXiv:0901.1842v2, p. 22, Lemma 8.6

import Mathlib
import Definitions.Def_SmallGainISS_OmegaPath_GainOperator

open scoped NNReal
open Filter Topology

namespace SmallGainISS.OmegaPath

/-- Lemma 8.6 (p. 22).
(i) For `D = diag(ρ)`, `ρ ∈ 𝒦∞`, `ρ > id`, there are sequences `ρ₁⁽ᵏ⁾, ρ₂⁽ᵏ⁾ ∈ 𝒦∞`, `ρᵢ⁽ᵏ⁾ > id`,
with `D = D₁⁽ᵏ⁾ ∘ D₂⁽ᵏ⁾` for every `k`, chosen so that `D₂⁽ᵏ⁾(s) < D₂⁽ᵏ⁺¹⁾(s)` for all `0 < s`.
(ii) For `D = diag(id + α)`, `α ∈ 𝒦∞`, there are `α₁, α₂ ∈ 𝒦∞` with
`D = diag(id + α₁) ∘ diag(id + α₂)`. -/
theorem lemma_8_6 (n : ℕ) :
    (∀ ρ : ℝ≥0 → ℝ≥0, SmallGainISS.Lyapunov.IsKInf ρ → GtId ρ →
      ∃ ρ₁ ρ₂ : ℕ → ℝ≥0 → ℝ≥0,
        (∀ k, SmallGainISS.Lyapunov.IsKInf (ρ₁ k) ∧ SmallGainISS.Lyapunov.IsKInf (ρ₂ k) ∧ GtId (ρ₁ k) ∧ GtId (ρ₂ k) ∧
          (diagOp (n := n) ρ = diagOp (ρ₁ k) ∘ diagOp (ρ₂ k))) ∧
        ∀ k, ∀ s : Fin n → ℝ≥0, SPos s → SmallGainISS.Lyapunov.SLt (diagOp (ρ₂ k) s) (diagOp (ρ₂ (k + 1)) s)) ∧
    (∀ α : ℝ≥0 → ℝ≥0, SmallGainISS.Lyapunov.IsKInf α →
      ∃ α₁ α₂ : ℝ≥0 → ℝ≥0, SmallGainISS.Lyapunov.IsKInf α₁ ∧ SmallGainISS.Lyapunov.IsKInf α₂ ∧
        diagOp (n := n) (fun r => r + α r) =
          diagOp (fun r => r + α₁ r) ∘ diagOp (fun r => r + α₂ r)) := by sorry

end SmallGainISS.OmegaPath
