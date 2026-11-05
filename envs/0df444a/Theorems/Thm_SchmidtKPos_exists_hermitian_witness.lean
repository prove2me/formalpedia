-- Prove2me | Theorems.Thm_SchmidtKPos_exists_hermitian_witness
-- name    : SchmidtKPos.exists_hermitian_witness
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:50:48.756596+00:00
-- url     : https://prove2.me/theorems/6396a56d-51f9-4233-9bd6-0ee3be068ac7
-- title:
--   Eq. (23), p.5 — a Hermitian operator separates $\rho\notin S_k$ from $S_k$
-- statement:
--   Let $\rho$ be a density matrix on $\mathcal H_n\otimes\mathcal H_n$ with $\rho\notin S_k$. Then there exists a Hermitian operator $H$ such that
--
--   $$
--   \operatorname{Tr}H\rho<0\quad\text{and}\quad\forall\sigma\in S_k\ \ \operatorname{Tr}H\sigma\ge 0 .
--   $$
--
--   This is the hyperplane $\{\sigma\in S\mid\operatorname{Tr}H\sigma=0\}$ separating the convex compact set $S_k$ from the point $\rho$. It is the first step of the "only if" half of Theorem 1.
--
--   Differences from the source:
--   - encoding: ≥ 0 and < 0 for a real quantity → the ComplexOrder relations on ℂ, which also assert that the value is real; reason: the quantity is real in every instance the source considers, so the condition is the same
--   - encoding: any decomposition {p_i ≥ 0, |ψ_i⟩} of ρ (Definition 1) → finite families indexed by Fin r, with unit vectors ψ_i and zero weights allowed; reason: in finite dimension a countable decomposition reduces to a finite one (Carathéodory) and a non-unit vector is absorbed into its weight; the same states result
--   - reading: the range of k (and of n in H_n) is left unstated → every natural number k and n, including 0; reason: never the weaker reading; at k = 0 the set S_0 is empty and at n = 0 there are no density matrices, so nothing is lost for k, n ≥ 1
-- source:
--   B. M. Terhal, P. Horodecki, A Schmidt number for density matrices, arXiv:quant-ph/9911117v4, p. 5, Eq. (23)

import Mathlib
import Definitions.Def_SchmidtKPos_schmidtClass
open scoped Matrix ComplexConjugate ComplexOrder

namespace SchmidtKPos

/-- B. M. Terhal, P. Horodecki, *A Schmidt number for density matrices*,
arXiv:quant-ph/9911117v4, p.5, Eq. (23): for `ρ ∉ S_k` there is a Hermitian operator `H` with
`Tr Hρ < 0` and `Tr Hσ ≥ 0` for all `σ ∈ S_k`.

**Formalization Note.** `<` and `≤` on `ℂ` are the `ComplexOrder` ones, which include reality of
the trace. At `k = 0`, `S_0 = ∅` and the statement is still the paper's. -/
theorem exists_hermitian_witness {n k : ℕ} (ρ : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (hρ : QAlgorithms.IsDensityMatrix ρ) (hk : ρ ∉ schmidtClass n k) :
    ∃ H : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ, H.IsHermitian ∧
      (H * ρ).trace < 0 ∧ ∀ σ ∈ schmidtClass n k, 0 ≤ (H * σ).trace := by sorry

end SchmidtKPos
