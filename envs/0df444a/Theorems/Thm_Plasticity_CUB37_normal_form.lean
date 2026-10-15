-- Prove2me | Theorems.Thm_Plasticity_CUB37_normal_form
-- name    : Plasticity.CUB37.normal_form
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-14T09:01:28.234093+00:00
-- url     : https://prove2.me/theorems/8c73e8c2-46c7-46df-b42f-ef3cff698c71
-- title:
--   Normal form: after a signed coordinate bijection every coordinate moves inward
-- statement:
--   Let $X$ be a space between $c_{00}(\Gamma)$ and $c_0(\Gamma)$, $Y$ one between $c_{00}(\Delta)$ and $c_0(\Delta)$, and $F\colon B_X\to B_Y$ a nonexpansive bijection of their closed unit balls (supremum norm). No assumption is made on $F^{-1}$.
--   Then there are a bijection $\sigma\colon\Gamma\to\Delta$ and signs $\alpha_n\in\{1,-1\}$ such that, for every $x\in B_X$ and every $n\in\Gamma$, the number
--   $$H(x)_n=\alpha_n\,F(x)_{\sigma(n)}$$
--   lies between $0$ and $x_n$: $0\le H(x)_n\le x_n$ if $x_n\ge0$, and $x_n\le H(x)_n\le0$ if $x_n\le0$.
--
--   In words, $F$ is a signed coordinate bijection followed by a map that moves every coordinate weakly towards zero without changing its sign. This is the first step of the proof that such bijections are signed bijections.
--
--   **Formalization Note** Spaces are submodules of $\ell_\infty$ as in the definitions `Plasticity_SeqSpace`; balls are `ballIn`. Index sets may be empty.
-- source:
--   This repository: expositions/c0_between_spaces.md §2, Proposition 1 (N1); after Leo's Lemmas 3.1–3.4 (R. Leo, Plasticity of the unit ball of c and c₀, J. Math. Anal. Appl. 2022)

import Definitions.Def_Plasticity_SeqSpace
import Mathlib.Topology.EMetricSpace.Lipschitz

namespace Plasticity.CUB37
theorem normal_form {Γ Δ : Type*} (X : Submodule ℝ (Linf Γ)) (Y : Submodule ℝ (Linf Δ))
    (hX0 : c00 Γ ≤ X) (hX1 : X ≤ c0 Γ) (hY0 : c00 Δ ≤ Y) (hY1 : Y ≤ c0 Δ)
    (F : Linf Γ → Linf Δ)
    (hbij : Set.BijOn F (ballIn X) (ballIn Y))
    (hlip : LipschitzOnWith 1 F (ballIn X)) :
    ∃ σ : Γ ≃ Δ, ∃ α : Γ → ℝ, (∀ n, α n = 1 ∨ α n = -1) ∧
      ∀ x ∈ ballIn X, ∀ n, (0 ≤ x n → 0 ≤ α n * F x (σ n) ∧ α n * F x (σ n) ≤ x n) ∧
        (x n ≤ 0 → x n ≤ α n * F x (σ n) ∧ α n * F x (σ n) ≤ 0) := by sorry
end Plasticity.CUB37
