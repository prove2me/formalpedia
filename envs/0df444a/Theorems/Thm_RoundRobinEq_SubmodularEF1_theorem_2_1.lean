-- Prove2me | Theorems.Thm_RoundRobinEq_SubmodularEF1_theorem_2_1
-- name    : RoundRobinEq.SubmodularEF1.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:18:33.250433+00:00
-- url     : https://prove2.me/theorems/3b34e2e8-6c77-4474-812b-cf9b6ccf04fe
-- title:
--   Theorem 2.1 — (Nemhauser et al.) v is non-decreasing submodular iff v(T) ≤ v(S) + Σ_{g∈T∖S} v(g | S)
-- statement:
--   Let $M$ be a finite set of goods and $v:2^M\to\mathbb R_{\ge0}$ a non-negative set function, with marginal values $v(g\mid S)=v(S\cup\{g\})-v(S)$. Then $v$ is non-decreasing and submodular if and only if
--   $$v(T)\ \le\ v(S)+\sum_{g\in T\setminus S} v(g\mid S)\qquad\text{for all } S,T\subseteq M .$$
--
--   This characterization of monotone submodular functions, due to Nemhauser, Wolsey and Fisher, is the first step of the closing bound in the proof of Theorem 4.4, where it bounds the value of a bundle by the value of agent $i$'s deviation bundle plus a sum of marginal values.
--
--   **Formalization Note** $v$ is a real-valued function on `Finset M` with the hypothesis $v(S)\ge0$ for all $S$ (the paper's codomain $\mathbb R_{\ge0}$); normalization $v(\emptyset)=0$ is not assumed, as in the paper's statement. "Submodular" is the marginal form of p. 5 (`IsSubmodular`).
-- source:
--   Amanatidis et al., Round-Robin Beyond Additive Agents, arXiv:2301.13652v1, p. 5, Theorem 2.1

import Mathlib
import Definitions.Def_RoundRobinEq_SubmodularEF1_Setting

namespace RoundRobinEq.SubmodularEF1

/-- Theorem 2.1 (Nemhauser et al.), p. 5: a function `v : 2^M → ℝ≥0` is non-decreasing and
submodular iff `v(T) ≤ v(S) + ∑_{g ∈ T \ S} v(g | S)` for all `S, T ⊆ M`. -/
theorem theorem_2_1 {M : Type} [Fintype M] [DecidableEq M] (v : Finset M → ℝ)
    (hv : ∀ S, 0 ≤ v S) :
    (IsNonDecreasing v ∧ IsSubmodular v) ↔
      ∀ S T : Finset M, v T ≤ v S + ∑ g ∈ T \ S, marginal v {g} S := by sorry

end RoundRobinEq.SubmodularEF1
