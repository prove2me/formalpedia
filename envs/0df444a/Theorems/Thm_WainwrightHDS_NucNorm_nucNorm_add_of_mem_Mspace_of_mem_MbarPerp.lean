-- Prove2me | Theorems.Thm_WainwrightHDS_NucNorm_nucNorm_add_of_mem_Mspace_of_mem_MbarPerp
-- name    : WainwrightHDS.NucNorm.nucNorm_add_of_mem_Mspace_of_mem_MbarPerp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:32:02.679293+00:00
-- url     : https://prove2.me/theorems/f001df3a-f0eb-4563-a1c8-e4488467630a
-- title:
--   §10.2.1 — decomposability of the nuclear norm: $|||A+B|||_{\mathrm{nuc}}=|||A|||_{\mathrm{nuc}}+|||B|||_{\mathrm{nuc}}$
-- statement:
--   Let $\mathbb U\subseteq\mathbb R^{d_1}$ and $\mathbb V\subseteq\mathbb R^{d_2}$ be linear subspaces. If $A\in\mathbb M(\mathbb U,\mathbb V)$ (row space in $\mathbb V$, column space in $\mathbb U$) and $B\in\overline{\mathbb M}^\perp(\mathbb U,\mathbb V)$ (row space in $\mathbb V^\perp$, column space in $\mathbb U^\perp$), then
--
--   $$
--   |||A+B|||_{\mathrm{nuc}} \;=\; |||A|||_{\mathrm{nuc}} + |||B|||_{\mathrm{nuc}} .
--   $$
--
--   This is the decomposability of the nuclear norm with respect to the pair $(\mathbb M,\overline{\mathbb M}^\perp)$, the structural property that lets the general theory of decomposable regularizers apply to low-rank matrix estimation.
--
--   Differences from the source:
--   - generalization: U, V r-dimensional subspaces (spanned by the first r columns of orthonormal U, V) → arbitrary subspaces U, V; reason: the identity holds for every pair of subspaces, so it specializes to the source's r-dimensional pairs
--   - encoding: rowspan(Θ), colspan(Θ) → ranges of x ↦ Θᵀx and z ↦ Θz on Euclidean spaces; indices 0-based; reason: Lean convention; same instances
-- source:
--   Wainwright, High-Dimensional Statistics: A Non-Asymptotic Viewpoint, Cambridge University Press 2019, doi:10.1017/9781108627771, §10.2.1, p. 318 (PDF p. 338), display following (10.14)

import Mathlib
import Definitions.Def_WainwrightHDS_NucNorm_nucNorm
import Definitions.Def_WainwrightHDS_NucNorm_Mspace
import Definitions.Def_WainwrightHDS_NucNorm_MbarPerp

namespace WainwrightHDS.NucNorm

/-- **Decomposability of the nuclear norm.** For `A ∈ 𝕄(𝕌, 𝕍)` and `B ∈ 𝕄̄⊥(𝕌, 𝕍)`,
`|||A + B|||_nuc = |||A|||_nuc + |||B|||_nuc`.
Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*, Cambridge University
Press 2019, §10.2.1, p. 318 (PDF p. 338), display following (10.14).

Formalization Note: `𝕌`, `𝕍` are arbitrary subspaces of `ℝ^{d₁}`, `ℝ^{d₂}` (the book takes
`r`-dimensional ones); this is a generalization containing the book's case. -/
theorem nucNorm_add_of_mem_Mspace_of_mem_MbarPerp {d₁ d₂ : ℕ}
    (U : Submodule ℝ (EuclideanSpace ℝ (Fin d₁))) (V : Submodule ℝ (EuclideanSpace ℝ (Fin d₂)))
    (A B : Matrix (Fin d₁) (Fin d₂) ℝ) (hA : A ∈ Mspace U V) (hB : B ∈ MbarPerp U V) :
    nucNorm (A + B) = nucNorm A + nucNorm B := by sorry

end WainwrightHDS.NucNorm
