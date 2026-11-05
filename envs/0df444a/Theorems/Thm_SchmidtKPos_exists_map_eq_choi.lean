-- Prove2me | Theorems.Thm_SchmidtKPos_exists_map_eq_choi
-- name    : SchmidtKPos.exists_map_eq_choi
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:47:43.031233+00:00
-- url     : https://prove2.me/theorems/51fe062b-d425-4dbe-8b86-c7052144c2be
-- title:
--   Eq. (24), p.5 — every Hermitian $H$ equals $(\mathbf 1\otimes\Lambda)(|\Psi^+\rangle\langle\Psi^+|)$
-- statement:
--   Let $H$ be a Hermitian operator on $\mathcal H_n\otimes\mathcal H_n$. Then there is a linear Hermiticity-preserving map $\Lambda:\mathcal M_n(\mathbb C)\to\mathcal M_n(\mathbb C)$ with
--
--   $$
--   H=(\mathbf 1\otimes\Lambda)(|\Psi^+\rangle\langle\Psi^+|),\qquad |\Psi^+\rangle=\frac1{\sqrt n}\sum_{i=1}^n|ii\rangle .
--   $$
--
--   This associates to the separating operator of Eq. (23) the linear map that the proof of Theorem 1 goes on to show is $k$-positive.
--
--   **Formalization Note** The vector $|\Psi^+\rangle$ is the published `Information100.P67.maximallyEntangledKey n`, with the same formula.
--
--   Differences from the source:
--   - reading: We define Λ as H = (1 ⊗ Λ_k)(|Ψ+⟩⟨Ψ+|) → existence of a linear Λ : M_n → M_n with this property that preserves Hermiticity; reason: the page later calls Λ_k k-positive, which by Definition 2 includes Hermiticity preservation
--   - reading: the range of k (and of n in H_n) is left unstated → every natural number k and n, including 0; reason: never the weaker reading; at k = 0 the set S_0 is empty and at n = 0 there are no density matrices, so nothing is lost for k, n ≥ 1
-- source:
--   B. M. Terhal, P. Horodecki, A Schmidt number for density matrices, arXiv:quant-ph/9911117v4, p. 5, Eq. (24)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P50
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67
open scoped Matrix ComplexConjugate ComplexOrder

namespace SchmidtKPos

open QAlgorithms.Papers.Independent.Dependency50.P50 (PreservesHermiticity)
open QAlgorithms.Papers.Independent.Information100.P67 (maximallyEntangledKey)

/-- B. M. Terhal, P. Horodecki, *A Schmidt number for density matrices*,
arXiv:quant-ph/9911117v4, p.5, Eq. (24): every Hermitian `H` on `H_n ⊗ H_n` is
`(1 ⊗ Λ)(|Ψ⁺⟩⟨Ψ⁺|)` for a linear Hermiticity-preserving `Λ`.

**Formalization Note.** The paper says "We define `Λ` as `H = (1 ⊗ Λ_k)(|Ψ⁺⟩⟨Ψ⁺|)`"; the map is
`Λ(E_ij) = n · H_ij`, with `H_ij` the `(i, j)` block of `H`. Hermiticity preservation is implicit
on the page (`Λ_k` is called `k`-positive, which by Definition 2 includes it) and is stated here. `|Ψ⁺⟩ = n^{-1/2} Σ_i |ii⟩` is the published
`Information100.P67.maximallyEntangledKey n`. -/
theorem exists_map_eq_choi {n : ℕ} (H : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (hH : H.IsHermitian) :
    ∃ Λ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ,
      PreservesHermiticity Λ ∧
        QAlgorithms.idTensorSuperop (R := Fin n) (⇑Λ)
          (QAlgorithms.pureDensity (maximallyEntangledKey n)) = H := by sorry

end SchmidtKPos
