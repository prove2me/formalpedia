-- Prove2me | Theorems.Thm_QMAPlusGap_lemma_14
-- name    : QMAPlusGap.lemma_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:09:56.132777+00:00
-- url     : https://prove2.me/theorems/1c80d658-a425-4d1f-90c3-897c53db0ca0
-- title:
--   Lemma 14 — approximating the high-eigenvalue part
-- statement:
--   Let $\Gamma_m$ be a density operator supported on $\mathrm{Sym}^m(\mathcal H)$, fix $1\le\ell\le m$, let $\rho_\ell$ be its reduced state on $\ell$ registers, let $P\ne0$ be an orthogonal projector on $\mathcal H$ and write $\rho_P=P^{\otimes\ell}\rho_\ell P^{\otimes\ell}$. There is a subnormalized mixture $\tilde\rho_P$ of states $(|\psi\rangle\langle\psi|)^{\otimes\ell}$ with $|\psi\rangle\in P\mathcal H$ such that
--   $$
--   \operatorname{Tr}\tilde\rho_P=\operatorname{Tr}\rho_P,\qquad \|\rho_P-\tilde\rho_P\|_1\ \le\ \frac{8\ell\sqrt{\operatorname{rank}P-1}}{m}.
--   $$
--
--   With $P=\mathbf 1_{(1/m,1]}(\rho_1)$, whose rank is at most $m$, this gives a trace-norm error $8\ell/\sqrt m$ independent of $\dim\mathcal H$.
--
--   Differences from the source:
--   - encoding: a subnormalized mixture of states (|ψ⟩⟨ψ|)^{⊗ℓ} with |ψ⟩ ∈ PH → ∫(|ψ⟩⟨ψ|)^{⊗ℓ} dν for a finite measure ν concentrated on unit vectors with Pψ = ψ; reason: a subnormalized mixture is a finite measure on such states; its mass is Tr ρ̃_P = Tr ρ_P ≤ 1
-- source:
--   Miyamoto, Near-Optimal Gap Amplification for Nonnegative Unentangled Quantum Proofs, arXiv:2608.07986 (held version, sha256 4667925f…), Lemma 14, p.27 (restated p.36)

import Mathlib
import Definitions.Def_QMAPlusGap_IsSymSupported
import Definitions.Def_QMAPlusGap_reduce
import Definitions.Def_WildeQIT_Schumacher_tensorPow
import Definitions.Def_QMAPlusGap_IsOrthProj
import Definitions.Def_ArgmaxDeFinetti_vnorm
import Definitions.Def_QMAPlusGap_tpMixture
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_traceNorm

set_option autoImplicit false

open scoped MatrixOrder ComplexOrder
open MeasureTheory Filter Matrix

namespace QMAPlusGap

/-- **Lemma 14 (Approximating the high-eigenvalue part)**, Miyamoto, *Near-Optimal Gap Amplification for Nonnegative Unentangled Quantum Proofs*, arXiv:2608.07986 (held version, sha256 4667925f…), p.27 (restated p.36): "Let Γ_m be a density operator
supported on Sym^m(H). Fix 1 ≤ ℓ ≤ m, and let ρ_ℓ be its reduced state on ℓ registers. Let P be a nonzero
orthogonal projector on H, and write ρ_P = P^{⊗ℓ} ρ_ℓ P^{⊗ℓ}. There is a subnormalized mixture ρ̃_P of states
(|ψ⟩⟨ψ|)^{⊗ℓ}, with |ψ⟩ ∈ PH, such that Tr ρ̃_P = Tr ρ_P, ∥ρ_P − ρ̃_P∥₁ ≤ 8ℓ√(rank P − 1)/m."

**Formalization Note** The mixture is `ρ̃_P = ∫ (|ψ⟩⟨ψ|)^{⊗ℓ} dν(ψ)` for a finite measure `ν` concentrated on unit
vectors with `Pψ = ψ`; its total mass is then `Tr ρ̃_P = Tr ρ_P ≤ 1` (subnormalized). `rank P` is
`Matrix.rank P`. -/
theorem lemma_14 {ι : Type} [Fintype ι] [DecidableEq ι] (m ℓ : ℕ) (hℓ1 : 1 ≤ ℓ) (hℓm : ℓ ≤ m)
    (Γ : Matrix (Fin m → ι) (Fin m → ι) ℂ) (hΓ : WildeQIT.IsDensityOperator Γ) (hΓs : IsSymSupported Γ)
    (P : Matrix ι ι ℂ) (hP : IsOrthProj P) (hP0 : P ≠ 0) :
    ∃ ν : Measure (ι → ℂ), IsFiniteMeasure ν ∧ (∀ᵐ ψ ∂ν, ArgmaxDeFinetti.vnorm ψ = 1 ∧ P *ᵥ ψ = ψ) ∧
      Matrix.trace (tpMixture ℓ ν) = Matrix.trace (WildeQIT.Schumacher.tensorPow ℓ P * reduce ℓ Γ * WildeQIT.Schumacher.tensorPow ℓ P) ∧
      WildeQIT.traceNorm (WildeQIT.Schumacher.tensorPow ℓ P * reduce ℓ Γ * WildeQIT.Schumacher.tensorPow ℓ P - tpMixture ℓ ν) ≤
        8 * (ℓ : ℝ) * Real.sqrt ((P.rank : ℝ) - 1) / (m : ℝ) := by sorry

end QMAPlusGap
