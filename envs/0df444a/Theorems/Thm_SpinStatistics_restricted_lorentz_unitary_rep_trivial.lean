-- Prove2me | Theorems.Thm_SpinStatistics_restricted_lorentz_unitary_rep_trivial
-- name    : SpinStatistics.restricted_lorentz_unitary_rep_trivial
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-24T13:51:45.142977+00:00
-- url     : https://prove2.me/theorems/5e3e8fe0-b7d4-467b-86d8-ba59cae8f717
-- title:
--   The restricted Lorentz group has no non-trivial finite-dimensional unitary representations
-- statement:
--   Let $SO^+(1,3)$ be the restricted (proper, orthochronous) Lorentz group: real $4\times4$ matrices $\Lambda$ with $\Lambda^{\mathsf T}\eta\Lambda=\eta$, $\det\Lambda=1$ and $\Lambda_{00}\ge1$, where $\eta=\mathrm{diag}(1,-1,-1,-1)$. Let $n\ge 0$ and let
--   $$\rho : SO^+(1,3)\longrightarrow U(n)$$
--   be a continuous group homomorphism into the group of $n\times n$ complex unitary matrices, i.e. a finite-dimensional continuous unitary representation. Then $\rho$ is trivial:
--   $$\rho(\Lambda)=I_n\qquad\text{for all }\Lambda\in SO^+(1,3).$$
--
--   This is the representation-theoretic fact quoted in the source: *the Lorentz group has no non-trivial unitary representations of finite dimension*. It is why a relativistic Hilbert space of particle states with finite non-zero spin and a positive, Lorentz-invariant norm cannot be built naively, and why integer-spin theories need gauge symmetry to discard negative-norm polarisations, while half-integer spin is handled by Fermi statistics.
--
--   **Formalization Note.** $\rho$ is a function on all of $M_4(\mathbb R)$, but it is only required to be multiplicative and continuous on $SO^+(1,3)$, and the conclusion concerns only $SO^+(1,3)$. The source says "the Lorentz group"; the statement uses the identity component, because the full group $O(1,3)$ has non-trivial one-dimensional unitary characters ($\Lambda\mapsto\det\Lambda$ and $\Lambda\mapsto\operatorname{sign}\Lambda_{00}$), so the literal claim is false for it. Continuity is the standard convention for representations of Lie groups. Every $n$-dimensional complex Hilbert space is isometric to $\mathbb C^n$, so matrices are used.
-- source:
--   Wikipedia, "Spin–statistics theorem" (https://en.wikipedia.org/wiki/Spin%E2%80%93statistics_theorem), PDF snapshot supplied by the proposal owner; section 'Relation to representation theory of the Lorentz group', p. 4, first sentence

import Mathlib
import Definitions.Def_SpinStatistics_Defs

namespace SpinStatistics

theorem restricted_lorentz_unitary_rep_trivial (n : ℕ)
    (ρ : Matrix (Fin 4) (Fin 4) ℝ → Matrix.unitaryGroup (Fin n) ℂ)
    (hmul : ∀ A ∈ restrictedLorentzSet, ∀ B ∈ restrictedLorentzSet,
      ρ (A * B) = ρ A * ρ B)
    (hcont : ContinuousOn ρ restrictedLorentzSet) :
    ∀ Λ ∈ restrictedLorentzSet, ρ Λ = 1 := by sorry

end SpinStatistics
