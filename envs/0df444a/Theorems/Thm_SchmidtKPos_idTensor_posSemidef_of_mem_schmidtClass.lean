-- Prove2me | Theorems.Thm_SchmidtKPos_idTensor_posSemidef_of_mem_schmidtClass
-- name    : SchmidtKPos.idTensor_posSemidef_of_mem_schmidtClass
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:51:54.99707+00:00
-- url     : https://prove2.me/theorems/9aba3880-2dab-4f22-a18f-0ed6f798c4f5
-- title:
--   p.5, "if" part of Theorem 1 — $k$-positive maps keep $(\mathbf 1\otimes\Lambda)(\rho)\ge 0$ on $S_k$
-- statement:
--   Let $\Lambda:\mathcal M_n(\mathbb C)\to\mathcal M_m(\mathbb C)$ be $k$-positive and let $\rho\in S_k$. Then
--
--   $$
--   (\mathbf 1\otimes\Lambda)(\rho)\ge 0 .
--   $$
--
--   This is the "if" half of Theorem 1: no $k$-positive map can detect a density matrix of Schmidt number at most $k$.
--
--   Differences from the source:
--   - generalization: Λ_k acting on H_n ⊗ H_n, with output dimension not named → any linear Λ : M_n → M_m; reason: the argument does not use m = n; m = n gives the source statement
--   - encoding: any decomposition {p_i ≥ 0, |ψ_i⟩} of ρ (Definition 1) → finite families indexed by Fin r, with unit vectors ψ_i and zero weights allowed; reason: in finite dimension a countable decomposition reduces to a finite one (Carathéodory) and a non-unit vector is absorbed into its weight; the same states result
--   - reading: 1 ⊗ Λ of Definition 2, the dimension of 1 unnamed → the identity acts on H_n, the input dimension of Λ (S_k lives on H_n ⊗ H_n); reason: Definition 2 quantifies over S_k, which p.1 defines on H_n ⊗ H_n
--   - reading: the range of k (and of n in H_n) is left unstated → every natural number k and n, including 0; reason: never the weaker reading; at k = 0 the set S_0 is empty and at n = 0 there are no density matrices, so nothing is lost for k, n ≥ 1
-- source:
--   B. M. Terhal, P. Horodecki, A Schmidt number for density matrices, arXiv:quant-ph/9911117v4, p. 5, proof of Theorem 1, "if" part

import Mathlib
import Definitions.Def_SchmidtKPos_IsKPositive
open scoped Matrix ComplexConjugate ComplexOrder

namespace SchmidtKPos

/-- B. M. Terhal, P. Horodecki, *A Schmidt number for density matrices*,
arXiv:quant-ph/9911117v4, p.5, proof of Theorem 1, "if" part: a `k`-positive map keeps every
`ρ ∈ S_k` positive under `1 ⊗ Λ`.

**Formalization Note.** The output dimension `m` is arbitrary (the proof does not use `m = n`). -/
theorem idTensor_posSemidef_of_mem_schmidtClass {n m k : ℕ}
    (Λ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ) (hΛ : IsKPositive k Λ)
    (ρ : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) (hρ : ρ ∈ schmidtClass n k) :
    (QAlgorithms.idTensorSuperop (R := Fin n) (⇑Λ) ρ).PosSemidef := by sorry

end SchmidtKPos
