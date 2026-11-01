-- Prove2me | Theorems.Thm_WildeQIT_Gentle_theorem_9_5_1
-- name    : WildeQIT.Gentle.theorem_9_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:56:41.751982+00:00
-- url     : https://prove2.me/theorems/520ce93e-6c4d-4111-82bc-73ced6cf227b
-- title:
--   Theorem 9.5.1: entanglement fidelity $F_e(\rho,\mathcal N)=\sum_m|\mathrm{Tr}\{\rho K_m\}|^2$
-- statement:
--   Let $\rho_A$ be a density operator and let $\mathcal N:\mathcal L(\mathcal H_A)\to\mathcal L(\mathcal H_A)$ be a quantum channel with Kraus operators $\{K_m\}$. Then the entanglement fidelity of $\mathcal N$ on $\rho_A$ is
--
--   $$F_e(\rho,\mathcal N)=\sum_m\bigl|\operatorname{Tr}\{\rho_A K_m\}\bigr|^2 .$$
--
--   Here $F_e(\rho,\mathcal N)\equiv\langle\psi|\sigma|\psi\rangle$ with $\sigma_{RA}=(\mathrm{id}_R\otimes\mathcal N_A)(\psi_{RA})$ for a purification $|\psi\rangle_{RA}$ of $\rho_A$ (Definition 9.5.1). The statement has two parts:
--
--   1. the identity holds for the published entanglement fidelity, which uses the canonical purification $(I_R\otimes\sqrt{\rho_A})|\Gamma\rangle_{RA}$;
--   2. for every purification $|\psi\rangle_{RA}$ of $\rho_A$ on any finite reference system $R$, $\langle\psi|(\mathrm{id}_R\otimes\mathcal N_A)(\psi_{RA})|\psi\rangle=\sum_m|\operatorname{Tr}\{\rho_A K_m\}|^2$.
--
--   The formula computes how well a channel preserves entanglement directly from its Kraus operators.
--
--   **Formalization Note** A channel is the published Kraus-form `WildeQIT.QChannel`, so $\{K_m\}$ is its Kraus family; $\mathrm{id}_R\otimes\mathcal N$ is `QChannel.tensorIdApply`; $\langle\psi|\sigma|\psi\rangle$ is the published `WildeQIT.expectedFidelity`.
--
--   Differences from the source:
--   - encoding: $F_e(\rho,\mathcal N)$ defined with any purification (Definition 9.5.1, independence remarked on p. 282) → conjunction of the identity for the published canonical-purification `entanglementFidelity` and for every purification on every finite reference system; reason: together these are the book's quantity under every choice of purification.
--   - encoding: a channel $\mathcal N$ with a set of Kraus operators $\{K_m\}$ → a `QChannel`, which is the Kraus family; reason: Theorem 4.4.1 gives every channel this form, and the theorem is stated for a given Kraus set.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 9.5.1, eq. (9.229), p. 282; Definition 9.5.1, p. 281

import Definitions.Def_WildeQIT_entanglementFidelity
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_Gentle_IsPurification

open Matrix

namespace WildeQIT.Gentle

/-- **Theorem 9.5.1** (Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8,
p. 282, eq. (9.229)). Let `ρ_A ∈ D(H_A)` and let `N : L(H_A) → L(H_A)` be a quantum channel with
Kraus operators `{K_m}`. Then the entanglement fidelity is
`F_e(ρ, N) = ∑_m |Tr{ρ_A K_m}|²`.

The statement has two parts: (1) for the published `WildeQIT.entanglementFidelity`, which
evaluates Definition 9.5.1 at the canonical purification `(I_R ⊗ √ρ)|Γ⟩`; (2) for every
purification `|ψ⟩_{RA}` of `ρ_A` on any finite reference system `R`, the value
`⟨ψ|(id_R ⊗ N)(ψ_{RA})|ψ⟩` of Definition 9.5.1 (p. 281), which allows any purification.

**Formalization Note.** A channel is the published Kraus-form `WildeQIT.QChannel`, so `{K_m}` is
the family `N.K`; `id_R ⊗ N` is `QChannel.tensorIdApply`; `⟨ψ|σ|ψ⟩` is the published
`WildeQIT.expectedFidelity`; `|ψ⟩⟨ψ|` is `vecMulVec ψ (star ψ)`. -/
theorem theorem_9_5_1 {a : Type} [Fintype a] [DecidableEq a]
    (ρ : Matrix a a ℂ) (hρ : IsDensityOperator ρ) (N : QChannel a a) :
    entanglementFidelity ρ N = ∑ m, ‖(ρ * N.K m).trace‖ ^ 2 ∧
    ∀ (r : Type) [Fintype r] [DecidableEq r] (ψ : r × a → ℂ), IsPurification ψ ρ →
      expectedFidelity ψ (N.tensorIdApply r (vecMulVec ψ (star ψ))) =
        ∑ m, ‖(ρ * N.K m).trace‖ ^ 2 := by sorry

end WildeQIT.Gentle
