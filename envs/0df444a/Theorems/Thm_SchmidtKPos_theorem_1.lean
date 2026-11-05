-- Prove2me | Theorems.Thm_SchmidtKPos_theorem_1
-- name    : SchmidtKPos.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:52:03.385298+00:00
-- url     : https://prove2.me/theorems/c9e9c810-b1fe-45dc-b34c-9d12fef1c500
-- title:
--   Theorem 1 — a density matrix on $\mathcal H_n\otimes\mathcal H_n$ has Schmidt number at least $k+1$ iff some $k$-positive map $\Lambda$ has $(\mathbf 1\otimes\Lambda)(\rho)\not\ge 0$
-- statement:
--   Let $\rho$ be a density matrix on $\mathcal H_n\otimes\mathcal H_n$. Then $\rho$ has Schmidt number at least $k+1$ if and only if there exists a $k$-positive linear map $\Lambda_k:\mathcal M_n(\mathbb C)\to\mathcal M_m(\mathbb C)$ (for some $m$) such that
--
--   $$
--   (\mathbf 1\otimes\Lambda_k)(\rho)\not\ge 0 .
--   $$
--
--   Moreover, when $\rho$ has Schmidt number at least $k+1$, such a map can be chosen with $m=n$.
--
--   For $k=1$ this is the characterization of entanglement by positive maps; for general $k$ it says that $k$-positive maps witness the Schmidt number. Here $k$-positive is Definition 2 of the paper: a linear Hermiticity-preserving map with $(\mathbf 1\otimes\Lambda)(|\psi\rangle\langle\psi|)\ge 0$ for all $|\psi\rangle\langle\psi|\in S_k$.
--
--   Differences from the source:
--   - encoding: any decomposition {p_i ≥ 0, |ψ_i⟩} of ρ (Definition 1) → finite families indexed by Fin r, with unit vectors ψ_i and zero weights allowed; reason: in finite dimension a countable decomposition reduces to a finite one (Carathéodory) and a non-unit vector is absorbed into its weight; the same states result
--   - encoding: Schmidt number at least k+1 → ∃ j, k + 1 ≤ j ∧ HasSchmidtNumber ρ j; reason: Definition 1 is a relation, so this is its literal reading and no junk value arises
--   - reading: a k-positive linear map Λ_k, output dimension unnamed in the statement → the iff ranges over Λ : M_n → M_m for every m; reason: Λ_k acts on half of ρ, so its input is M_n; its output is not fixed, so the "if" half is stated for every m (never the weaker reading)
--   - generalization: ∃ k-positive Λ_k with (1 ⊗ Λ_k)(ρ) ≱ 0 → a second conjunct: such Λ exists with Λ : M_n → M_n; reason: the proof constructs Λ_k on M_n (Eq. (24)); this implies the existential of the iff with m = n
--   - reading: 1 ⊗ Λ of Definition 2, the dimension of 1 unnamed → the identity acts on H_n, the input dimension of Λ (S_k lives on H_n ⊗ H_n); reason: Definition 2 quantifies over S_k, which p.1 defines on H_n ⊗ H_n
--   - reading: the range of k (and of n in H_n) is left unstated → every natural number k and n, including 0; reason: never the weaker reading; at k = 0 the set S_0 is empty and at n = 0 there are no density matrices, so nothing is lost for k, n ≥ 1
-- source:
--   B. M. Terhal, P. Horodecki, A Schmidt number for density matrices, arXiv:quant-ph/9911117v4, Theorem 1, Eq. (3), p. 2

import Mathlib
import Definitions.Def_SchmidtKPos_IsKPositive
open scoped Matrix ComplexConjugate ComplexOrder

namespace SchmidtKPos

/-- B. M. Terhal, P. Horodecki, *A Schmidt number for density matrices*,
arXiv:quant-ph/9911117v4, Theorem 1, p.2: let `ρ` be a density matrix on `H_n ⊗ H_n`. Then `ρ`
has Schmidt number at least `k + 1` iff there exists a `k`-positive linear map `Λ_k` such that
`(1 ⊗ Λ_k)(ρ) ≱ 0` (Eq. (3)).

**Formalization Note.** "Schmidt number at least `k + 1`" is Definition 1 literally. `Λ_k` acts on
half of `ρ`, so it has input `M_n`; the theorem does not name its output dimension, so the first
conjunct is the iff over every `Λ : M_n → M_m` (the "if" half holds for every `m`). The second
conjunct records that the witness can be taken with `m = n`, as the proof constructs it on `M_n`
(Eq. (24)). `k`-positive is Definition 2. No hypothesis on `n` or `k` is needed: at `k = 0` both
sides hold (`Λ = −id`), and for `k ≥ n` both fail. -/
theorem theorem_1 {n k : ℕ} (ρ : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (hρ : QAlgorithms.IsDensityMatrix ρ) :
    ((∃ j, k + 1 ≤ j ∧ HasSchmidtNumber ρ j) ↔
      ∃ (m : ℕ) (Λ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ),
        IsKPositive k Λ ∧
          ¬ (QAlgorithms.idTensorSuperop (R := Fin n) (⇑Λ) ρ).PosSemidef) ∧
    ((∃ j, k + 1 ≤ j ∧ HasSchmidtNumber ρ j) →
      ∃ Λ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ,
        IsKPositive k Λ ∧
          ¬ (QAlgorithms.idTensorSuperop (R := Fin n) (⇑Λ) ρ).PosSemidef) := by sorry

end SchmidtKPos
