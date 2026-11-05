-- Prove2me | Theorems.Thm_SchmidtKPos_lemma_3_dual
-- name    : SchmidtKPos.lemma_3_dual
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:52:11.852853+00:00
-- url     : https://prove2.me/theorems/2204e3a7-f437-4da1-8dd3-ddfc7fd23cdc
-- title:
--   Lemma 3, last clause, p.4 — the dual of a $k$-positive map is $k$-positive
-- statement:
--   If $\Lambda:\mathcal M_n(\mathbb C)\to\mathcal M_m(\mathbb C)$ is $k$-positive, then the dual map $\Lambda^\dagger:\mathcal M_m(\mathbb C)\to\mathcal M_n(\mathbb C)$, defined by $\operatorname{Tr}A^\dagger\Lambda(B)=\operatorname{Tr}\Lambda^\dagger(A^\dagger)B$ for all $A$ and $B$, is also $k$-positive.
--
--   This final step lets the proof of Theorem 1 take $\Lambda^\dagger$ as the detecting map.
--
--   **Formalization Note** For $\Lambda^\dagger$, Definition 2 tests vectors in $\mathbb C^m\otimes\mathbb C^m$, since the input of $\Lambda^\dagger$ is $\mathcal M_m(\mathbb C)$.
--
--   Differences from the source:
--   - generalization: Λ in Lemma 3, with dimensions not named, used on M_n → M_n in the proof of Theorem 1 → any linear Λ : M_n → M_m; reason: the argument does not use m = n; m = n gives the source statement
--   - reading: 1 ⊗ Λ of Definition 2, the dimension of 1 unnamed → the identity acts on H_n, the input dimension of Λ (S_k lives on H_n ⊗ H_n); reason: Definition 2 quantifies over S_k, which p.1 defines on H_n ⊗ H_n
--   - encoding: any decomposition {p_i ≥ 0, |ψ_i⟩} of ρ (Definition 1) → finite families indexed by Fin r, with unit vectors ψ_i and zero weights allowed; reason: in finite dimension a countable decomposition reduces to a finite one (Carathéodory) and a non-unit vector is absorbed into its weight; the same states result
--   - reading: the range of k (and of n in H_n) is left unstated → every natural number k and n, including 0; reason: never the weaker reading; at k = 0 the set S_0 is empty and at n = 0 there are no density matrices, so nothing is lost for k, n ≥ 1
-- source:
--   B. M. Terhal, P. Horodecki, A Schmidt number for density matrices, arXiv:quant-ph/9911117v4, Lemma 3, last clause, p. 4

import Mathlib
import Definitions.Def_SchmidtKPos_IsKPositive
import Definitions.Def_SchmidtKPos_dualMap
open scoped Matrix ComplexConjugate ComplexOrder

namespace SchmidtKPos

/-- B. M. Terhal, P. Horodecki, *A Schmidt number for density matrices*,
arXiv:quant-ph/9911117v4, Lemma 3, last clause, p.4: if `Λ` is `k`-positive, then `Λ†` is
`k`-positive.

**Formalization Note.** `Λ : M_n → M_m` may be rectangular; then `Λ† : M_m → M_n` is tested with
ancilla `H_m`, as Definition 2 prescribes for a map with input `M_m`. -/
theorem lemma_3_dual {n m k : ℕ}
    (Λ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ) (hΛ : IsKPositive k Λ) :
    IsKPositive k (dualMap Λ) := by sorry

end SchmidtKPos
