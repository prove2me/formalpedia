-- Prove2me | Theorems.Thm_WhitneyMatroid_Fano_proportional_of_inZ_circuit
-- name    : WhitneyMatroid.Fano.proportional_of_inZ_circuit
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T05:13:16.818066+00:00
-- url     : https://prove2.me/theorems/1934c83d-4fb0-489e-882a-9a72558946dc
-- title:
--   Lemma 11 — two points of $H$ supported on the same circuit are proportional
-- statement:
--   Let $\mathbf M'$ be a real matrix with matroid $M'$, let $\mathbf M$ be a circuit matrix of $\mathbf M'$, and let $H$ be the subspace spanned by the rows of $\mathbf M$. If $P=e_{i_1}+\cdots+e_{i_p}$ is a circuit of $M'$ and $(b_1,\dots,b_n)$, $(b'_1,\dots,b'_n)$ are points of $H$ that are both in $Z_{i_1\cdots i_p}$, then the two are proportional:
--
--   $$
--   (b'_1,\dots,b'_n)=c\,(b_1,\dots,b_n)\qquad\text{for some real } c\neq 0.
--   $$
--
--   In particular the row of a circuit in a circuit matrix is determined up to a nonzero factor. Whitney uses this rigidity to normalise the matrix (16.3) in §16.
-- source:
--   Whitney, On the Abstract Properties of Linear Dependence, Amer. J. Math. 57 (1935), p. 528, Lemma 11

import Mathlib
import Definitions.Def_WhitneyMatroid_Fano_IsMatroidOf
import Definitions.Def_WhitneyMatroid_Fano_IsCircuitMatrix

namespace WhitneyMatroid.Fano

/-- Whitney, Lemma 11 (p. 528). Let `B` (Whitney's `𝐌`) be the circuit matrix of the real matrix
`A` (Whitney's `𝐌′`), whose matroid is `M′`, and let `H` be the subspace spanned by the rows of
`B`. If `P = {i₁, …, i_p}` is a circuit of `M′` and the points `b`, `b′` of `H` are both in
`Z_{i₁⋯i_p}`, then they are proportional: `b′ = c • b` for some nonzero real `c`. -/
theorem proportional_of_inZ_circuit {ι : Type*} [Fintype ι] {m : ℕ} {κ : Type*}
    (A : Matrix (Fin m) ι ℝ) (M' : Matroid ι) (B : Matrix κ ι ℝ)
    (row : κ ≃ {P : Set ι // M'.IsCircuit P}) (hB : IsCircuitMatrix M' A B row)
    (P : Set ι) (hP : M'.IsCircuit P) (b b' : ι → ℝ)
    (hb : b ∈ Submodule.span ℝ (Set.range B)) (hb' : b' ∈ Submodule.span ℝ (Set.range B))
    (hbP : InZ b P) (hb'P : InZ b' P) :
    ∃ c : ℝ, c ≠ 0 ∧ b' = c • b := by sorry

end WhitneyMatroid.Fano
