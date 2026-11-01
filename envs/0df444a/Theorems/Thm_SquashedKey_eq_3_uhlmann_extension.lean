-- Prove2me | Theorems.Thm_SquashedKey_eq_3_uhlmann_extension
-- name    : SquashedKey.eq_3_uhlmann_extension
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:28:57.080748+00:00
-- url     : https://prove2.me/theorems/b3331862-4059-4f32-9f13-5ba5ecbdfc79
-- title:
--   Eq. (3) — Uhlmann: an extension of $\rho_A$ can be matched by an extension of $\sigma_A$ with the same fidelity
-- statement:
--   Let $A$ and $B$ be quantum systems of arbitrary dimension, $\rho_A,\sigma_A$ states on $A$, and $\rho_{AB}$ an extension of $\rho_A$, i.e. $\operatorname{Tr}_B\rho_{AB}=\rho_A$. Then there is an extension $\sigma_{AB}$ of $\sigma_A$ ($\operatorname{Tr}_B\sigma_{AB}=\sigma_A$) on the same system $B$ with
--   $$
--   F(\rho_A,\sigma_A)=F(\rho_{AB},\sigma_{AB}),
--   $$
--   where $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1^2$ is the fidelity.
--
--   In the proof of Theorem 2 this transfers the closeness of $\gamma$ and $\omega$ to their extensions.
--
--   **Formalization Note** Hilbert spaces are $\ell^2$ of arbitrary index types; $F$ is the published trace-class squared fidelity, valued in $[0,+\infty]$.
--
--   Differences from the source:
--
--   - encoding: Hilbert spaces of any dimension → ℓ²(I) for an arbitrary index type I (no finiteness or countability), operators as coefficient arrays, states as the published trace-class State I; reason: every Hilbert space has an orthonormal basis and is ℓ² of its index set; the same instances
--   - encoding: F(ρ,σ) = ‖√ρ√σ‖₁² as a real number → published traceClassSquaredFidelity, valued in ℝ≥0∞; reason: the fidelity is a nonnegative real ≤ 1; an equality of the same numbers
-- source:
--   Wilde, Squashed entanglement and approximate private states, arXiv:1606.08028v3, eq. (3), p.4

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P08
import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P02

open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Frontier18.P08 (partialTraceSecond)
open QAlgorithms.Papers.Independent.Intakenext100.P02 (traceClassSquaredFidelity)

namespace SquashedKey

/-- **Uhlmann extension, (3)**, Wilde, *Squashed entanglement and approximate private states*,
arXiv:1606.08028v3, §2.2, (3), p.4 (PDF p.4): "Uhlmann's theorem also implies that, for a given
extension of `ρ_AB` of `ρ_A`, there exists an extension `σ_AB` of `σ_A` such that
`F(ρ_A, σ_A) = F(ρ_AB, σ_AB)`."

For all types `A`, `B`, all states `ρ_A`, `σ_A` on `A` and every state `ρ_AB` on `A × B` with
`Tr_B ρ_AB = ρ_A`, there is a state `σ_AB` on `A × B` with `Tr_B σ_AB = σ_A` and
`F(ρ_A, σ_A) = F(ρ_AB, σ_AB)`.

**Formalization Note** Hilbert spaces are `ℓ²` of arbitrary index types (no finiteness or
countability); `F(ρ, σ) = ‖√ρ √σ‖₁²` is the published `traceClassSquaredFidelity`, valued in
`ℝ≥0∞`; `Tr_B` is `partialTraceSecond`. The extending system `B` is the same on both sides. -/
theorem eq_3_uhlmann_extension {A B : Type} (ρA σA : State A) (ρAB : State (A × B))
    (hρ : partialTraceSecond ρAB.coefficients = ρA.coefficients) :
    ∃ σAB : State (A × B), partialTraceSecond σAB.coefficients = σA.coefficients ∧
      traceClassSquaredFidelity ρA σA = traceClassSquaredFidelity ρAB σAB := by sorry

end SquashedKey
