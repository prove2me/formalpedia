-- Prove2me | Theorems.Thm_PowerSeries_exists_sum_smul_eq_of_forall_coeff_mem
-- name    : PowerSeries.exists_sum_smul_eq_of_forall_coeff_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/8ef1c969-2db9-5fe4-96a1-0fce51f7d9b3
-- title:
--   Descent of coefficients in K₀-linear combinations of power series
-- statement:
--   Let $L$ be a field and $K_0 \subseteq L$ a subfield. Let $n$ be a natural number and let $g : \mathrm{Fin}\,n \to L[[X]]$ be a family of formal power series over $L$ such that for every index $i$ and every $m \in \mathbb{N}$ the coefficient of $X^m$ in $g_i$ lies in $K_0$. Let $c : \mathrm{Fin}\,n \to L$ be scalars such that every coefficient of the power series $\sum_i c_i \cdot g_i$ lies in $K_0$. The assertion is that there exists a family $c' : \mathrm{Fin}\,n \to L$ with $c'_i \in K_0$ for every $i$ and with the equality of power series $\sum_i c'_i \cdot g_i = \sum_i c_i \cdot g_i$. Thus a combination of power series with coefficients in $K_0$ which happens to have all its coefficients in $K_0$ can be rewritten, without changing its value, using scalars from $K_0$; the new scalars are produced as elements of $L$ together with the assertion that they belong to the subfield, and no claim is made that $c'_i = c_i$ or that $c'$ is unique.
--
--   This is the standard fact that solvability of a linear system over a field is unaffected by passing to a field extension (Rouché–Capelli), in the form needed for $q$-expansions. It is used in the treatment of the $K_0$-rational structure on spaces of modular forms, by the statements about $q$-expansion coefficients on modular curves that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PowerSeries_exists_sum_smul_eq_of_forall_coeff_mem.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PowerSeries.exists_sum_smul_eq_of_forall_coeff_mem
    {L : Type} [Field L] (K₀ : Subfield L) {n : ℕ} (g : Fin n → PowerSeries L)
    (hg : ∀ (i : Fin n) (m : ℕ), (g i).coeff m ∈ K₀)
    (c : Fin n → L) (h : ∀ m : ℕ, (∑ i, c i • g i).coeff m ∈ K₀) :
    ∃ c' : Fin n → L, (∀ i, c' i ∈ K₀) ∧ ∑ i, c' i • g i = ∑ i, c i • g i := by sorry
