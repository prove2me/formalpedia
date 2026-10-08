-- Prove2me | Theorems.Thm_WhitneyMatroid_Fano_support_isUnion_circuits
-- name    : WhitneyMatroid.Fano.support_isUnion_circuits
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T05:12:49.028929+00:00
-- url     : https://prove2.me/theorems/e417d565-ac8b-4f72-8eba-3a40282fa187
-- title:
--   Lemma 10 — the support of a point of $H$ is a union of circuits
-- statement:
--   Let $\mathbf M'$ be a real matrix with matroid $M'$, let $\mathbf M$ be a circuit matrix of $\mathbf M'$, and let $H$ be the hyperplane (linear subspace) of $\mathbb R^n$ spanned by the rows of $\mathbf M$. Let $(b_1,\dots,b_n)$ be a point of $H$ lying in $Z_{i_1\cdots i_p}$, i.e. with $b_j\neq 0$ exactly for $j\in\{i_1,\dots,i_p\}$. Then
--
--   $$
--   N'=e_{i_1}+\cdots+e_{i_p}\ \text{ is the union of a set of circuits of } M'.
--   $$
--
--   Here $e_i$ in $M'$ corresponds to the column $C_i$. The lemma says that the supports of vectors in the row space of a circuit matrix are exactly built from circuits; it is used to produce circuits from vectors in Lemma 11 and Theorem 32.
--
--   **Formalization Note** The point of $H$ is any vector in the real span of the rows of $\mathbf M$. A union of circuits is the union of a family (possibly empty, for the zero vector) of circuits of $M'$.
-- source:
--   Whitney, On the Abstract Properties of Linear Dependence, Amer. J. Math. 57 (1935), p. 528, Lemma 10

import Mathlib
import Definitions.Def_WhitneyMatroid_Fano_IsMatroidOf
import Definitions.Def_WhitneyMatroid_Fano_IsCircuitMatrix

namespace WhitneyMatroid.Fano

/-- Whitney, Lemma 10 (p. 528). Let `B` (Whitney's `𝐌`) be the circuit matrix of the real matrix
`A` (Whitney's `𝐌′`), whose matroid is `M′`, and let `H` be the subspace spanned by the rows of
`B`. If a point `b` of `H` is in `Z_{i₁⋯i_p}`, i.e. its set of nonzero coordinates is
`N′ = {i₁, …, i_p}`, then `N′` is the union of a set of circuits of `M′`. -/
theorem support_isUnion_circuits {ι : Type*} [Fintype ι] {m : ℕ} {κ : Type*}
    (A : Matrix (Fin m) ι ℝ) (M' : Matroid ι) (B : Matrix κ ι ℝ)
    (row : κ ≃ {P : Set ι // M'.IsCircuit P}) (hB : IsCircuitMatrix M' A B row)
    (b : ι → ℝ) (hb : b ∈ Submodule.span ℝ (Set.range B)) (N' : Set ι) (hbN : InZ b N') :
    ∃ 𝒞 : Set (Set ι), (∀ C ∈ 𝒞, M'.IsCircuit C) ∧ ⋃₀ 𝒞 = N' := by sorry

end WhitneyMatroid.Fano
