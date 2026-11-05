-- Prove2me | Theorems.Thm_SchmidtKPos_kPositive_of_choi_nonneg
-- name    : SchmidtKPos.kPositive_of_choi_nonneg
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:51:51.708968+00:00
-- url     : https://prove2.me/theorems/be4e294e-d7ee-4e85-ba89-e33f7dd2ba0b
-- title:
--   Eqs. (25)–(26), p.5 — nonnegativity of $H$ on $S_k$ makes $\Lambda$ $k$-positive
-- statement:
--   Let $\Lambda:\mathcal M_n(\mathbb C)\to\mathcal M_n(\mathbb C)$ be linear and let $H=(\mathbf 1\otimes\Lambda)(|\Psi^+\rangle\langle\Psi^+|)$ be Hermitian. If
--
--   $$
--   \operatorname{Tr}H\sigma\ge 0\qquad\text{for all }\sigma\in S_k,
--   $$
--
--   then $\Lambda$ is $k$-positive.
--
--   This is the step of the proof of Theorem 1 that turns the separating operator of Eq. (23) into a $k$-positive map.
--
--   Differences from the source:
--   - reading: the argument of Eqs. (24)–(26) for the H of Eq. (23) → a standalone implication with hypotheses H Hermitian, H = (1 ⊗ Λ)(|Ψ+⟩⟨Ψ+|), and Tr Hσ ≥ 0 on S_k; reason: these are exactly the properties of H the page uses; ρ plays no part in this step
--   - encoding: ≥ 0 and < 0 for a real quantity → the ComplexOrder relations on ℂ, which also assert that the value is real; reason: the quantity is real in every instance the source considers, so the condition is the same
--   - reading: 1 ⊗ Λ of Definition 2, the dimension of 1 unnamed → the identity acts on H_n, the input dimension of Λ (S_k lives on H_n ⊗ H_n); reason: Definition 2 quantifies over S_k, which p.1 defines on H_n ⊗ H_n
--   - encoding: any decomposition {p_i ≥ 0, |ψ_i⟩} of ρ (Definition 1) → finite families indexed by Fin r, with unit vectors ψ_i and zero weights allowed; reason: in finite dimension a countable decomposition reduces to a finite one (Carathéodory) and a non-unit vector is absorbed into its weight; the same states result
--   - reading: the range of k (and of n in H_n) is left unstated → every natural number k and n, including 0; reason: never the weaker reading; at k = 0 the set S_0 is empty and at n = 0 there are no density matrices, so nothing is lost for k, n ≥ 1
-- source:
--   B. M. Terhal, P. Horodecki, A Schmidt number for density matrices, arXiv:quant-ph/9911117v4, p. 5, Eqs. (25)–(26)

import Mathlib
import Definitions.Def_SchmidtKPos_IsKPositive
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67
open scoped Matrix ComplexConjugate ComplexOrder

namespace SchmidtKPos

open QAlgorithms.Papers.Independent.Information100.P67 (maximallyEntangledKey)

/-- B. M. Terhal, P. Horodecki, *A Schmidt number for density matrices*,
arXiv:quant-ph/9911117v4, p.5, Eqs. (25)–(26): if `H = (1 ⊗ Λ)(|Ψ⁺⟩⟨Ψ⁺|)` is Hermitian and
`Tr Hσ ≥ 0` for all `σ ∈ S_k`, then `Λ` is `k`-positive.

**Formalization Note.** No bound on `k` is needed: for `k ≥ n`, `H ≥ 0` and `Λ` is completely
positive. `H.IsHermitian` is what gives Hermiticity preservation, in particular at `k = 0`. `|Ψ⁺⟩ = n^{-1/2} Σ_i |ii⟩` is the published
`Information100.P67.maximallyEntangledKey n`. -/
theorem kPositive_of_choi_nonneg {n k : ℕ}
    (Λ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ)
    (H : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) (hH : H.IsHermitian)
    (hΛ : QAlgorithms.idTensorSuperop (R := Fin n) (⇑Λ)
      (QAlgorithms.pureDensity (maximallyEntangledKey n)) = H)
    (hpos : ∀ σ ∈ schmidtClass n k, 0 ≤ (H * σ).trace) :
    IsKPositive k Λ := by sorry

end SchmidtKPos
