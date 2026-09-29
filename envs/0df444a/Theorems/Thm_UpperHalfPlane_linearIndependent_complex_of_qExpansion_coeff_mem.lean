-- Prove2me | Theorems.Thm_UpperHalfPlane_linearIndependent_complex_of_qExpansion_coeff_mem
-- name    : UpperHalfPlane.linearIndependent_complex_of_qExpansion_coeff_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/86f7f158-b9cb-57fe-bb1f-df7bb12cab0e
-- title:
--   Linear independence over K descends from q-expansion coefficients to ℂ
-- statement:
--   Let $N$ be a positive natural number, let $K$ be an intermediate field of $\mathbb{Q} \subseteq \mathbb{C}$, let $\iota$ be an arbitrary index type, and let $f : \iota \to (\mathfrak{H} \to \mathbb{C})$ be a family of complex-valued functions on the upper half-plane. Assume that for each index $i$ the function $f_i$ is holomorphic, in the sense of being differentiable as a map between complex manifolds modelled on $\mathbb{C}$, and that there exists an exponent $m \in \mathbb{N}$ such that the product $f_i \cdot \Delta^m$, with $\Delta$ the discriminant modular form, satisfies the following three conditions: its extension to $\mathbb{C}$ by `UpperHalfPlane.ofComplex` is periodic with period $N$; it is bounded at $i\infty$; and every coefficient of its $q$-expansion of level $N$, i.e. its power series in $q_N = e^{2\pi i \tau / N}$, lies in $K$. Assume further that the family $f$ is linearly independent over $K$, as a family in the $K$-module of functions $\mathfrak{H} \to \mathbb{C}$. Then $f$ is linearly independent over $\mathbb{C}$.
--
--   This is a coefficientwise base-change statement for $q$-expansions: $\mathbb{C}$ is free over $K$, so a $\mathbb{C}$-linear relation among families whose $q$-coefficient columns are $K$-valued is a $\mathbb{C}$-combination of $K$-linear relations, and injectivity of the $q$-expansion map on holomorphic, $N$-periodic, bounded functions transfers relations among coefficients back to relations among the functions. It is used in the $q$-expansion-principle arguments for cusp forms, in particular by [`CuspForm.exists_qCoeff_alSlash_heckeULinH_add_qCoeff_diamondLinH_eq_mul_of_mem_twoCuspLattice`](thm.html#CuspForm.exists_qCoeff_alSlash_heckeULinH_add_qCoeff_diamondLinH_eq_mul_of_mem_twoCuspLattice), [`CuspForm.exists_ratCast_qCoeff_alSlash_of_forall_qCoeff_ratCast_gammaH`](thm.html#CuspForm.exists_ratCast_qCoeff_alSlash_of_forall_qCoeff_ratCast_gammaH) and [`WLight.exists_monicRel_j_K_of_mdifferentiable_frickeQuotient`](thm.html#WLight.exists_monicRel_j_K_of_mdifferentiable_frickeQuotient).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_UpperHalfPlane_linearIndependent_complex_of_qExpansion_coeff_mem.lean

import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.FieldTheory.IntermediateField.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped Manifold

theorem UpperHalfPlane.linearIndependent_complex_of_qExpansion_coeff_mem (N : ℕ) [NeZero N]
    (K : IntermediateField ℚ ℂ) {ι : Type*} (f : ι → UpperHalfPlane → ℂ)
    (hf : ∀ i, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f i) ∧ ∃ m : ℕ,
      Function.Periodic ((f i * ModularForm.discriminant ^ m) ∘ UpperHalfPlane.ofComplex) N ∧
      UpperHalfPlane.IsBoundedAtImInfty (f i * ModularForm.discriminant ^ m) ∧
      ∀ n : ℕ, (UpperHalfPlane.qExpansion N (f i * ModularForm.discriminant ^ m)).coeff n ∈ K)
    (hli : LinearIndependent ↥K f) : LinearIndependent ℂ f := by sorry
