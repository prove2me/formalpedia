-- Prove2me | Theorems.Thm_SchmidtKPos_trace_choi_mul_eq_dual
-- name    : SchmidtKPos.trace_choi_mul_eq_dual
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:48:23.32562+00:00
-- url     : https://prove2.me/theorems/7db06af5-ebee-4160-8d69-8b554daab85c
-- title:
--   Eq. (27), p.5 — $\operatorname{Tr}H\rho=\langle\Psi^+|(\mathbf 1\otimes\Lambda^\dagger)(\rho)|\Psi^+\rangle$
-- statement:
--   Let $\Lambda:\mathcal M_n(\mathbb C)\to\mathcal M_n(\mathbb C)$ be linear and put $H=(\mathbf 1\otimes\Lambda)(|\Psi^+\rangle\langle\Psi^+|)$. Then for every operator $\rho$ on $\mathcal H_n\otimes\mathcal H_n$,
--
--   $$
--   \operatorname{Tr}H\rho=\langle\Psi^+|\,(\mathbf 1\otimes\Lambda^\dagger)(\rho)\,|\Psi^+\rangle .
--   $$
--
--   Hence $\operatorname{Tr}H\rho<0$ is the inequality $\langle\Psi^+|(\mathbf 1\otimes\Lambda^\dagger)(\rho)|\Psi^+\rangle<0$ of Eq. (27), which shows that $(\mathbf 1\otimes\Lambda^\dagger)(\rho)$ is not positive semidefinite.
--
--   Differences from the source:
--   - generalization: Tr Hρ < 0 can be rewritten as ⟨Ψ+|(1 ⊗ Λ_k†)(ρ)|Ψ+⟩ < 0, Eq. (27) → the identity Tr Hρ = ⟨Ψ+|(1 ⊗ Λ†)(ρ)|Ψ+⟩ for every linear Λ and every matrix ρ; reason: equal numbers are negative together, so the printed equivalence follows at once
--   - reading: the range of k (and of n in H_n) is left unstated → every natural number k and n, including 0; reason: never the weaker reading; at k = 0 the set S_0 is empty and at n = 0 there are no density matrices, so nothing is lost for k, n ≥ 1
-- source:
--   B. M. Terhal, P. Horodecki, A Schmidt number for density matrices, arXiv:quant-ph/9911117v4, p. 5, Eq. (27)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_SchmidtKPos_dualMap
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67
open scoped Matrix ComplexConjugate ComplexOrder

namespace SchmidtKPos

open QAlgorithms.Papers.Independent.Information100.P67 (maximallyEntangledKey)

/-- B. M. Terhal, P. Horodecki, *A Schmidt number for density matrices*,
arXiv:quant-ph/9911117v4, p.5, Eq. (27): with `H = (1 ⊗ Λ)(|Ψ⁺⟩⟨Ψ⁺|)`,
`Tr Hρ = ⟨Ψ⁺|(1 ⊗ Λ†)(ρ)|Ψ⁺⟩`.

**Formalization Note.** The page states the consequence: `Tr Hρ < 0` "can be rewritten, using
Eq. (24), as" `⟨Ψ⁺|(1 ⊗ Λ_k†)(ρ)|Ψ⁺⟩ < 0`. This is the identity behind that rewriting, for every
`Λ` and every matrix `ρ`; it gives the printed equivalence at once. `|Ψ⁺⟩ = n^{-1/2} Σ_i |ii⟩` is the published
`Information100.P67.maximallyEntangledKey n`. -/
theorem trace_choi_mul_eq_dual {n : ℕ}
    (Λ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ)
    (ρ : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) :
    (QAlgorithms.idTensorSuperop (R := Fin n) (⇑Λ)
        (QAlgorithms.pureDensity (maximallyEntangledKey n)) * ρ).trace =
      star (WithLp.ofLp (maximallyEntangledKey n)) ⬝ᵥ
        (QAlgorithms.idTensorSuperop (R := Fin n) (⇑(dualMap Λ)) ρ *ᵥ
          WithLp.ofLp (maximallyEntangledKey n)) := by sorry

end SchmidtKPos
