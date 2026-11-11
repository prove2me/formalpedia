-- Prove2me | Theorems.Thm_UnitalMIP_proposition_3_8
-- name    : UnitalMIP.proposition_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T10:40:59.32893+00:00
-- url     : https://prove2.me/theorems/42d6573b-5abb-4697-8c11-7de1189ef84c
-- title:
--   Proposition 3.8 — boundary canonical form $\Psi_\lambda$ at $\rho_{\max}=1$; separable iff $\lambda=0$
-- statement:
--   Let $\psi\in M_2\otimes M_2$ be a state with maximally mixed marginals and $\rho_{\max}(\psi)=1$. Then $\psi$ is locally unitarily equivalent to
--
--   $$
--   \Psi_\lambda=\tfrac12\bigl(|00\rangle\langle00|+|11\rangle\langle11|+\lambda|00\rangle\langle11|+\lambda|11\rangle\langle00|\bigr)
--   $$
--
--   for some $\lambda\in[0,1]$. Moreover, $\psi$ is separable if and only if $\lambda=0$.
--
--   At the boundary $\rho_{\max}=1$ the whole family is one-parameter, which splits the second regime into its separable and entangled cases.
--
--   **Formalization Note** The second sentence is stated for every $\lambda\in[0,1]$ with $\psi$ equivalent to $\Psi_\lambda$.
--
--   Differences from the source:
--   - reading: “ψ is locally unitarily equivalent to Ψλ for some λ ∈ [0, 1]. Moreover, ψ is separable ⟺ λ = 0” → existence of such a $\lambda$, and the equivalence for every $\lambda\in[0,1]$ with $\psi$ equivalent to $\Psi_\lambda$; reason: the equivalence does not depend on which such $\lambda$ is chosen; this is the stronger reading of “Moreover”
--   - encoding: $\rho_{\max}$ as a maximum (Definition 2.20) → `sSup` of the set of admissible values $|\mathrm{Tr}[\psi(X\otimes Y^\dagger)]|$; reason: the set is nonempty and bounded and the maximum is attained by compactness, so the supremum equals it
--   - generalization: the §1.1 standing assumption (“Throughout, let ψ be a fixed two-qubit state … and assume that its entries are computable in polynomial time”, p.4) → any two-qubit density matrix ψ with the stated properties, with no computability hypothesis; reason: the statement concerns only the canonical form and separability; it specializes to the source's claim on every computable ψ
-- source:
--   Dong, Jiang, Qin, Yao, Zhou, A Dichotomy for MIP* in the Presence of Unital Noise, arXiv:2609.39318 (version of 2026-11-03, sha256 56ebc59e…), Proposition 3.8, p.30; proof, pp.69–70

import Mathlib
import Definitions.Def_UnitalMIP_HasMaxMixedMarginals
import Definitions.Def_UnitalMIP_rhoMax
import Definitions.Def_UnitalMIP_canonicalState

open scoped Matrix

namespace UnitalMIP

/-- **Proposition 3.8** (Boundary canonical form; Dong, Jiang, Qin, Yao, Zhou, *A Dichotomy for MIP* in the Presence of Unital Noise*, arXiv:2609.39318 (version of 2026-11-03, sha256 56ebc59e…), p.30; proved p.69). Let `ψ ∈ M₂ ⊗ M₂` have
maximally mixed marginals and `ρmax(ψ) = 1`. Then `ψ` is locally unitarily equivalent to `Ψ_λ` for
some `λ ∈ [0, 1]`. Moreover, `ψ` is separable if and only if `λ = 0`.

**Formalization Note** The second sentence is stated for every `λ ∈ [0, 1]` with `ψ` locally
unitarily equivalent to `Ψ_λ` (so it does not depend on which such `λ` is chosen). `ψ` is a density
matrix; `Ψ_λ` is (27). -/
theorem proposition_3_8 (ψ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hψ : QAlgorithms.IsDensityMatrix ψ) (hmm : HasMaxMixedMarginals ψ) (h1 : rhoMax ψ = 1) :
    (∃ lam : ℝ, 0 ≤ lam ∧ lam ≤ 1 ∧ IsLUEquiv ψ (PsiBoundary lam)) ∧
      ∀ lam : ℝ, 0 ≤ lam → lam ≤ 1 → IsLUEquiv ψ (PsiBoundary lam) →
        (QAlgorithms.Entanglement.IsSeparableDensity ψ ↔ lam = 0) := by sorry

end UnitalMIP
