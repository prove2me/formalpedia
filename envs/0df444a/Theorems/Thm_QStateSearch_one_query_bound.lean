-- Prove2me | Theorems.Thm_QStateSearch_one_query_bound
-- name    : QStateSearch.one_query_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:17:09.125929+00:00
-- url     : https://prove2.me/theorems/d153fedc-ba27-498a-9fb4-e4956877e0f7
-- title:
--   Proof of Theorem 4 — one replaced query moves the state by at most $2\sqrt u$
-- statement:
--   Let $\psi\in\mathbb C^D$ be a unit vector.
--
--   1. Let $\Phi$ be a unit vector of the oracle-input register and a purifying register $W'$, let $u=\sum_w|\sum_i\overline{\psi_i}\Phi(i,w)|^2$ be the overlap of its oracle-input register with $\psi$, and $\Phi'=(R_\psi\otimes I)\Phi$. Then $\langle\Phi|\Phi'\rangle=1-2u$ and
--   $$
--   D\big(|\Phi\rangle\langle\Phi|,|\Phi'\rangle\langle\Phi'|\big)=\sqrt{1-|1-2u|^2}=2\sqrt{u(1-u)}\le2\sqrt u .
--   $$
--   2. For a controlled query on $\{0,1\}\times[D]\times W$ and a unit vector $\Phi$, let $u_1=\sum_w|\sum_i\overline{\psi_i}\Phi(1,i,w)|^2$ be the weight on $|1\rangle\otimes|\psi\rangle$. Then $u_1\le u$ for the overlap $u$ of the oracle-input register with $\psi$, and with $\Phi'=\mathrm{c}\text{-}R_\psi\,\Phi$ the same identities hold with $u_1$, so $D(|\Phi\rangle\langle\Phi|,|\Phi'\rangle\langle\Phi'|)\le2\sqrt{u_1}\le2\sqrt u$.
--
--   Here $D(\rho,\sigma)=\frac12\|\rho-\sigma\|_1$. This is the per-query cost in the hybrid argument.
--
--   Differences from the source:
--   - encoding: a purification $|\Phi\rangle$ of the state before the query → a unit vector on $[D]\times W'$ for any finite $W'$ (uncontrolled) or on $\{0,1\}\times[D]\times W$ (controlled); reason: finite-dimensional purifications
--   - encoding: $D(\cdot,\cdot)=\frac12\|\cdot\|_1$ → $\frac12\cdot$`WildeQIT.traceDist`; reason: the published trace distance has no factor $\frac12$
-- source:
--   Barhoush, Quantum State Search with Classical Interactive Advice, arXiv:2610.25657 (held version, sha256 2a16939a…3408), proof of Theorem 4, second paragraph, p.13

import Mathlib
import Definitions.Def_QStateSearch_refl
import Definitions.Def_QStateSearch_ctrlQuery
import Definitions.Def_QStateSearch_overlap
import Definitions.Def_WildeQIT_traceDist
open Matrix
open scoped Kronecker

namespace QStateSearch

/-- **Proof of Theorem 4, one-query bound.** Let `ψ` be a unit vector, `Φ` a unit vector of the
oracle-input register and a purifying register, and `u` the overlap of its oracle-input register
with `ψ`. Then the two post-query purifications `Φ` and `(R_ψ ⊗ I)Φ` have inner product `1 − 2u`,
trace distance `√(1 − |1 − 2u|²) = 2√(u(1 − u)) ≤ 2√u`. For a controlled query on
`Fin 2 × Fin D × W`, `u` is replaced by the weight `u₁` on `|1⟩ ⊗ |ψ⟩`, which is at most the
overlap `u`, and the same bound holds.

Barhoush, *Quantum State Search with Classical Interactive Advice*, arXiv:2610.25657
(held version, sha256 2a16939a…3408), proof of Theorem 4, second paragraph, p.13.

**Formalization Note.** The trace distance is `½ · WildeQIT.traceDist` (`= ½‖·‖₁`), applied to the
pure states `|Φ⟩⟨Φ|`. The purifying register is any finite type `W'`; `R_ψ ⊗ I` is the Kronecker
product. `u = ∑_w |∑_i conj(ψ_i) Φ(i, w)|²`, and for the controlled query
`u₁ = ∑_w |∑_i conj(ψ_i) Φ(1, i, w)|²` while `overlap ψ Φ` also counts the control value `0`. -/
theorem one_query_bound {D : ℕ} (ψ : EuclideanSpace ℂ (Fin D)) (hψ : ‖ψ‖ = 1) :
    (∀ (W' : Type) [Fintype W'] [DecidableEq W'] (Φ : Fin D × W' → ℂ), ∑ x, ‖Φ x‖ ^ 2 = 1 →
      let u : ℝ := ∑ w, ‖∑ i, star (ψ i) * Φ (i, w)‖ ^ 2
      let Φ' := (refl ψ ⊗ₖ (1 : Matrix W' W' ℂ)) *ᵥ Φ
      star Φ ⬝ᵥ Φ' = ((1 - 2 * u : ℝ) : ℂ) ∧
      (1 / 2 : ℝ) * WildeQIT.traceDist (vecMulVec Φ (star Φ)) (vecMulVec Φ' (star Φ'))
        = Real.sqrt (1 - |1 - 2 * u| ^ 2) ∧
      Real.sqrt (1 - |1 - 2 * u| ^ 2) = 2 * Real.sqrt (u * (1 - u)) ∧
      2 * Real.sqrt (u * (1 - u)) ≤ 2 * Real.sqrt u) ∧
    (∀ (W : Type) [Fintype W] [DecidableEq W] (Φ : Reg D W → ℂ), ∑ x, ‖Φ x‖ ^ 2 = 1 →
      let u₁ : ℝ := ∑ w, ‖∑ i, star (ψ i) * Φ (1, i, w)‖ ^ 2
      let Φ' := ctrlQuery (W := W) (refl ψ) *ᵥ Φ
      u₁ ≤ overlap ψ Φ ∧
      star Φ ⬝ᵥ Φ' = ((1 - 2 * u₁ : ℝ) : ℂ) ∧
      (1 / 2 : ℝ) * WildeQIT.traceDist (vecMulVec Φ (star Φ)) (vecMulVec Φ' (star Φ'))
        = Real.sqrt (1 - |1 - 2 * u₁| ^ 2) ∧
      Real.sqrt (1 - |1 - 2 * u₁| ^ 2) = 2 * Real.sqrt (u₁ * (1 - u₁)) ∧
      2 * Real.sqrt (u₁ * (1 - u₁)) ≤ 2 * Real.sqrt u₁ ∧
      2 * Real.sqrt u₁ ≤ 2 * Real.sqrt (overlap ψ Φ)) := by sorry

end QStateSearch
