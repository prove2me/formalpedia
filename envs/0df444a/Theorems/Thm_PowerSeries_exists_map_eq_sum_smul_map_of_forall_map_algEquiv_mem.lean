-- Prove2me | Theorems.Thm_PowerSeries_exists_map_eq_sum_smul_map_of_forall_map_algEquiv_mem
-- name    : PowerSeries.exists_map_eq_sum_smul_map_of_forall_map_algEquiv_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/7c294533-b0e6-5a82-b68f-d8ae01d971c1
-- title:
--   Galois descent for E-subspaces of power series
-- statement:
--   Let $E$ be a field of characteristic zero, let $\iota \colon \overline{\mathbb{Q}} \to E$ be a ring homomorphism from the algebraic closure of $\mathbb{Q}$ used in the project, let $V$ be an $E$-submodule of the formal power series ring $E[[X]]$, and let $K$ be an intermediate field of $\overline{\mathbb{Q}}/\mathbb{Q}$ that is finite-dimensional over $\mathbb{Q}$. Let $A \in \overline{\mathbb{Q}}[[X]]$ be a formal power series such that every coefficient $\mathrm{coeff}\,n\,A$ lies in $K$, and assume that for every $\mathbb{Q}$-algebra automorphism $\sigma$ of $\overline{\mathbb{Q}}$ the series obtained from $A$ by applying $\iota \circ \sigma$ to all coefficients belongs to $V$. The conclusion asserts the existence of a natural number $n$, of elements $c_0,\dots,c_{n-1} \in \overline{\mathbb{Q}}$ indexed by `Fin n`, and of power series $r_0,\dots,r_{n-1} \in \mathbb{Q}[[X]]$, such that each $r_i$, read in $E[[X]]$ along the structure map $\mathbb{Q} \to E$, lies in $V$, and such that the series obtained from $A$ by applying $\iota$ coefficientwise satisfies $$A^{\iota} = \sum_{i} \iota(c_i) \cdot r_i^{\,\mathbb{Q} \to E}$$ in $E[[X]]$, the scalars $\iota(c_i) \in E$ acting by multiplication.
--
--   This is a Galois descent statement for $E$-linear subspaces of formal power series (a power-series form of Speiser's lemma): a series with coefficients in a number field all of whose Galois conjugates lie in $V$ is an $\overline{\mathbb{Q}}$-linear combination of series with rational coefficients lying in $V$. It is used in the analysis of $q$-expansions on modular curves, via [`ModularCurve.exists_slash_fricke_eq_sum_smul_of_ratCast_qExpansion`](thm.html#ModularCurve.exists_slash_fricke_eq_sum_smul_of_ratCast_qExpansion).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PowerSeries_exists_map_eq_sum_smul_map_of_forall_map_algEquiv_mem.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem PowerSeries.exists_map_eq_sum_smul_map_of_forall_map_algEquiv_mem
    {E : Type*} [Field E] [CharZero E] (ι : AlgebraicClosure ℚ →+* E)
    (V : Submodule E (PowerSeries E))
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (A : PowerSeries (AlgebraicClosure ℚ)) (hA : ∀ n : ℕ, PowerSeries.coeff n A ∈ K)
    (hV : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      A.map (ι.comp (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ∈ V) :
    ∃ (n : ℕ) (c : Fin n → AlgebraicClosure ℚ) (r : Fin n → PowerSeries ℚ),
      (∀ i, (r i).map (algebraMap ℚ E) ∈ V) ∧
        A.map ι = ∑ i, ι (c i) • (r i).map (algebraMap ℚ E) := by sorry
