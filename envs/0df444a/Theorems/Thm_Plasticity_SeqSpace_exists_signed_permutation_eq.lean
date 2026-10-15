-- Prove2me | Theorems.Thm_Plasticity_SeqSpace_exists_signed_permutation_eq
-- name    : Plasticity.SeqSpace.exists_signed_permutation_eq
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-15T08:00:45.384133+00:00
-- url     : https://prove2.me/theorems/96ddac85-cdda-4409-a4b6-3cf18783ad4a
-- title:
--   Nonexpansive bijections from balls between c₀₀ and c₀ onto balls between c₀₀ and ℓ∞ are signed permutations, wherever the target matches signs
-- statement:
--   Let $X$ be a linear subspace with $c_{00}(\Gamma)\subseteq X\subseteq c_0(\Gamma)$ and $Y$ one with $c_{00}(\Delta)\subseteq Y\subseteq\ell_\infty(\Delta)$, both with the supremum norm, and suppose that $X=c_{00}(\Gamma)$ or that $Y$ realizes every pattern of signs on every countable subset of $\Delta$. Then every nonexpansive bijection $F$ of the closed unit ball of $X$ onto that of $Y$ is the restriction of a signed permutation: $F(x)_{\sigma n}=\alpha_nx_n$ for a bijection $\sigma\colon\Gamma\to\Delta$ and signs $\alpha_n=\pm1$.
--   This is the card `Plasticity.CUB37` without its hypothesis $Y\subseteq c_0(\Delta)$, which the existence of $F$ forces (card `Plasticity.SeqSpace.le_c0_of_bijOn_ballIn`).
-- source:
--   This repository: claim CUB52 (claims/cub.md), with claim CUB37 and expositions/c0_between_spaces.md §§2–5 and §7

import Definitions.Def_Plasticity_SeqSpace
import Mathlib.Topology.EMetricSpace.Lipschitz

namespace Plasticity.SeqSpace
theorem exists_signed_permutation_eq {Γ Δ : Type*} (X : Submodule ℝ (Linf Γ)) (Y : Submodule ℝ (Linf Δ))
    (hX0 : c00 Γ ≤ X) (hX1 : X ≤ c0 Γ) (hY0 : c00 Δ ≤ Y)
    (hmatch : X = c00 Γ ∨ RealizesSignPatterns Y)
    (F : Linf Γ → Linf Δ)
    (hbij : Set.BijOn F (ballIn X) (ballIn Y))
    (hlip : LipschitzOnWith 1 F (ballIn X)) :
    ∃ σ : Γ ≃ Δ, ∃ α : Γ → ℝ, (∀ n, α n = 1 ∨ α n = -1) ∧
      ∀ x ∈ ballIn X, ∀ n, F x (σ n) = α n * x n := by sorry
end Plasticity.SeqSpace
