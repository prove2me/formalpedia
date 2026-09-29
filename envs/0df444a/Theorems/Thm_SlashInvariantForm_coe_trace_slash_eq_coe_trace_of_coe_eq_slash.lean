-- Prove2me | Theorems.Thm_SlashInvariantForm_coe_trace_slash_eq_coe_trace_of_coe_eq_slash
-- name    : SlashInvariantForm.coe_trace_slash_eq_coe_trace_of_coe_eq_slash
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/cbf25fa8-fac3-5b1e-a4b8-8461cf2bc875
-- title:
--   Atkin–Lehner equivariance of the trace of slash-invariant forms
-- statement:
--   Let $\mathcal G$ and $\mathcal H$ be subgroups of $\mathrm{GL}_2(\mathbb R)$ such that $\mathcal G$ has finite relative index in $\mathcal H$, i.e. the subgroup $\mathcal G\cap\mathcal H$ of $\mathcal H$ has finite index, and let $k$ be an integer. Let $F$ and $G$ be types of weight-$k$ slash-invariant forms for $\mathcal G$ (types with a `FunLike` map to functions $\mathbb H\to\mathbb C$ and a `SlashInvariantFormClass` structure for $\mathcal G$ and $k$, so that their elements satisfy $h\mid_k\gamma=h$ for all $\gamma\in\mathcal G$), and let $f:F$, $g:G$. Let $A,W\in\mathrm{GL}_2(\mathbb R)$ be such that: the function underlying $g$ is $f\mid_k A$; conjugation by $A$ and by $A^{-1}$ maps $\mathcal G$ into itself; conjugation by $W$ and by $W^{-1}$ maps $\mathcal H$ into itself; and $AW^{-1}\in\mathcal H$. Write $\mathrm{Tr}_{\mathcal H}$ for `SlashInvariantForm.trace ℋ`, the weight-$k$ slash-invariant form for $\mathcal H$ whose underlying function is the sum of $f\mid_k r^{-1}$ over the finite coset space $\mathcal H/(\mathcal G\cap\mathcal H)$. The conclusion is the equality of functions $\mathbb H\to\mathbb C$ $$\bigl(\mathrm{Tr}_{\mathcal H} f\bigr)\mid_k W=\mathrm{Tr}_{\mathcal H}\, g .$$
--
--   This is the classical compatibility of the trace (level-lowering) operator between two levels with an Atkin–Lehner or Fricke matrix normalising both levels: the trace intertwines the slash action of $A$ upstairs with that of $W$ downstairs. It is used in [`ModularForm.exists_coe_eq_slash_mul_alGL_and_coe_trace_slash_eq_coe_trace`](thm.html#ModularForm.exists_coe_eq_slash_mul_alGL_and_coe_trace_slash_eq_coe_trace), where the relevant $A$ is an Atkin–Lehner matrix at the larger level and $W$ the corresponding matrix at the smaller one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_SlashInvariantForm_coe_trace_slash_eq_coe_trace_of_coe_eq_slash.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem SlashInvariantForm.coe_trace_slash_eq_coe_trace_of_coe_eq_slash
    {𝒢 ℋ : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsFiniteRelIndex ℋ] {k : ℤ}
    {F G : Type*} [FunLike F UpperHalfPlane ℂ] [FunLike G UpperHalfPlane ℂ]
    [SlashInvariantFormClass F 𝒢 k] [SlashInvariantFormClass G 𝒢 k]
    (f : F) (g : G) (A W : GL (Fin 2) ℝ) (hg : (⇑g : UpperHalfPlane → ℂ) = (⇑f : UpperHalfPlane → ℂ) ∣[k] A)
    (hA : ∀ x ∈ 𝒢, A * x * A⁻¹ ∈ 𝒢) (hA' : ∀ x ∈ 𝒢, A⁻¹ * x * A ∈ 𝒢)
    (hW : ∀ x ∈ ℋ, W * x * W⁻¹ ∈ ℋ) (hW' : ∀ x ∈ ℋ, W⁻¹ * x * W ∈ ℋ) (hAW : A * W⁻¹ ∈ ℋ) :
    (⇑(SlashInvariantForm.trace ℋ f) : UpperHalfPlane → ℂ) ∣[k] W = ⇑(SlashInvariantForm.trace ℋ g) := by sorry
