-- Prove2me | Theorems.Thm_Plasticity_SeqSpace_exists_signed_permutation_inward
-- name    : Plasticity.SeqSpace.exists_signed_permutation_inward
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-15T03:19:50.084162+00:00
-- url     : https://prove2.me/theorems/a1cc2877-5f8f-468b-8965-770f36d97bae
-- title:
--   A nonexpansive bijection from a ball between c₀₀ and c₀ onto a ball between c₀₀ and ℓ∞ moves each coordinate inward along a signed permutation
-- statement:
--   Let $X$ be a linear subspace with $c_{00}(\Gamma)\subseteq X\subseteq c_0(\Gamma)$ and $Y$ one with $c_{00}(\Delta)\subseteq Y\subseteq\ell_\infty(\Delta)$, both with the supremum norm, and $F$ a nonexpansive bijection of the closed unit ball of $X$ onto that of $Y$. Then there are a bijection $\sigma\colon\Gamma\to\Delta$ and signs $\alpha_n=\pm1$ such that $\alpha_nF(x)_{\sigma n}$ lies between $0$ and $x_n$ for every $x$ in the ball and every $n$.
--   This is the normal form of CUB37(i) (Leo's Lemmas 3.1–3.7 for two spaces) with the target allowed anywhere between $c_{00}(\Delta)$ and $\ell_\infty(\Delta)$; the card `Plasticity.CUB37.normal_form` assumes $Y\subseteq c_0(\Delta)$, which its proof never uses.
-- source:
--   This repository: claim CUB52 (claims/cub.md), expositions/c0_between_spaces.md §2 and §7; N. Leo, J. Math. Anal. Appl. 507 (2022), Lemmas 3.1–3.7 (arXiv:2106.06276)

import Definitions.Def_Plasticity_SeqSpace
import Mathlib.Topology.EMetricSpace.Lipschitz

namespace Plasticity.SeqSpace
theorem exists_signed_permutation_inward {Γ Δ : Type*} (X : Submodule ℝ (Linf Γ)) (Y : Submodule ℝ (Linf Δ))
    (hX0 : c00 Γ ≤ X) (hX1 : X ≤ c0 Γ) (hY0 : c00 Δ ≤ Y)
    (F : Linf Γ → Linf Δ)
    (hbij : Set.BijOn F (ballIn X) (ballIn Y))
    (hlip : LipschitzOnWith 1 F (ballIn X)) :
    ∃ σ : Γ ≃ Δ, ∃ α : Γ → ℝ, (∀ n, α n = 1 ∨ α n = -1) ∧
      ∀ x ∈ ballIn X, ∀ n, (0 ≤ x n → 0 ≤ α n * F x (σ n) ∧ α n * F x (σ n) ≤ x n) ∧
        (x n ≤ 0 → x n ≤ α n * F x (σ n) ∧ α n * F x (σ n) ≤ 0) := by sorry
end Plasticity.SeqSpace
