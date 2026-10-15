-- Prove2me | Theorems.Thm_Plasticity_SeqSpace_le_c0_of_bijOn_ballIn
-- name    : Plasticity.SeqSpace.le_c0_of_bijOn_ballIn
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-15T08:00:31.047353+00:00
-- url     : https://prove2.me/theorems/d2882fce-6897-4d6f-8615-387b5de671f4
-- title:
--   A ball between c₀₀ and ℓ∞ that is the nonexpansive bijective image of a ball between c₀₀ and c₀ lies in c₀
-- statement:
--   Let $X$ be a linear subspace with $c_{00}(\Gamma)\subseteq X\subseteq c_0(\Gamma)$ and $Y$ one with $c_{00}(\Delta)\subseteq Y\subseteq\ell_\infty(\Delta)$, both with the supremum norm. If some nonexpansive bijection maps the closed unit ball of $X$ onto that of $Y$, then $Y\subseteq c_0(\Delta)$.
--   By the normal form, $|F(x)_{\sigma n}|\le|x_n|$ for a bijection $\sigma$, so every image point vanishes at infinity.
-- source:
--   This repository: claim CUB52 (claims/cub.md), expositions/c0_between_spaces.md §7

import Definitions.Def_Plasticity_SeqSpace
import Mathlib.Topology.EMetricSpace.Lipschitz

namespace Plasticity.SeqSpace
theorem le_c0_of_bijOn_ballIn {Γ Δ : Type*} (X : Submodule ℝ (Linf Γ)) (Y : Submodule ℝ (Linf Δ))
    (hX0 : c00 Γ ≤ X) (hX1 : X ≤ c0 Γ) (hY0 : c00 Δ ≤ Y)
    (F : Linf Γ → Linf Δ)
    (hbij : Set.BijOn F (ballIn X) (ballIn Y))
    (hlip : LipschitzOnWith 1 F (ballIn X)) :
    Y ≤ c0 Δ := by sorry
end Plasticity.SeqSpace
