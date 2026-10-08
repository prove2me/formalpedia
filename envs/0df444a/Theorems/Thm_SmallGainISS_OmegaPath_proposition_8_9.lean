-- Prove2me | Theorems.Thm_SmallGainISS_OmegaPath_proposition_8_9
-- name    : SmallGainISS.OmegaPath.proposition_8_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:15:14.551688+00:00
-- url     : https://prove2.me/theorems/c89b7bd4-53fb-4464-992c-a2c9f1f695bc
-- title:
--   Proposition 8.9 — $\Psi_\infty(T)$ meets every sphere $S_r$ and is unbounded
-- statement:
--   Let $n\ge1$ and let $T:\mathbb R^n_+\to\mathbb R^n_+$ be monotone and continuous with $T(s)\not\ge s$ for all $s\neq0$. Assume
--   $$\|s_k\|\to\infty\ \Longrightarrow\ \|T(s_k)\|\to\infty\qquad(k\to\infty)$$
--   for every sequence $(s_k)_{k\in\mathbb N}\subset\mathbb R^n_+$. Let $\Psi(T)=\{s:T(s)\le s\}$, $\Psi_\infty(T)=\bigcap_{k\ge0}T^k(\Psi(T))$ and $S_r=\{s\in\mathbb R^n_+:\sum_is_i=r\}$. Then
--   $$\Psi_\infty(T)\subset\Psi(T),\qquad \Psi_\infty(T)\cap S_r\neq\emptyset\ \text{ for all } r\ge0,\qquad \Psi_\infty(T)\ \text{is unbounded}.$$
--
--   The paper cites this result from Rüffer's earlier work ([25, Prop. 5.4]); it provides the unbounded backward orbit used to build the unbounded part of the path in Theorem 8.11.
--
--   **Formalization Note** The norm in the growth condition is the 1-norm; all norms on $\mathbb R^n$ are equivalent, so the condition does not depend on this choice. The case $n=0$ is excluded because $S_r$ is then empty for $r>0$.
-- source:
--   Dashkovskiy, Rüffer, Wirth, Small Gain Theorems for Large Scale Systems and Construction of ISS Lyapunov Functions, arXiv:0901.1842v2, p. 23, Proposition 8.9 (cited from [25, Prop. 5.4])

import Mathlib
import Definitions.Def_SmallGainISS_OmegaPath_GainOperator

open scoped NNReal
open Filter Topology

namespace SmallGainISS.OmegaPath

/-- Proposition 8.9 (p. 23, from [25, Prop. 5.4]). Let `T : ℝⁿ₊ → ℝⁿ₊`, `n ≥ 1`, be monotone and
continuous with `T(s) ≱ s` for all `s ≠ 0`, and assume (8.1): `‖sₖ‖ → ∞` implies `‖T(sₖ)‖ → ∞`
for every sequence in `ℝⁿ₊` (norm: the 1-norm). Then `Ψ∞(T) ⊂ Ψ(T)`, `Ψ∞(T) ∩ S_r ≠ ∅` for all
`r ≥ 0`, and `Ψ∞(T)` is unbounded. -/
theorem proposition_8_9 {n : ℕ} (hn : 0 < n) (T : (Fin n → ℝ≥0) → (Fin n → ℝ≥0))
    (hmono : Monotone T) (hcont : Continuous T) (hsgc : SGC T)
    (h81 : ∀ u : ℕ → Fin n → ℝ≥0, Tendsto (fun k => oneNorm (u k)) atTop atTop →
      Tendsto (fun k => oneNorm (T (u k))) atTop atTop) :
    PsiInf T ⊆ Psi T ∧ (∀ r : ℝ≥0, (PsiInf T ∩ sphereOne n r).Nonempty) ∧
    ¬ Bornology.IsBounded (PsiInf T) := by sorry

end SmallGainISS.OmegaPath
