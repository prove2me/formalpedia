-- Prove2me | Theorems.Thm_QStateSearch_hybrid_step
-- name    : QStateSearch.hybrid_step
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:20:25.183548+00:00
-- url     : https://prove2.me/theorems/24f7428e-2287-4bad-b136-8eb0d7f6cf96
-- title:
--   Proof of Theorem 4 — hybrid step $\mathbb E_\Psi D(\Omega^\Psi_{t-1},\Omega^\Psi_t)\le2\sqrt{(1+B\ln2)/D}$
-- statement:
--   Let $V$ be a classical-message verifier with at most $B$ padded prover bits, $\psi\mapsto P_\psi$ a measurable family of deterministic classical provers, and $t\in[q]$ a query. Let $\Omega^\psi_{t-1},\Omega^\psi_t$ be the final classical–quantum states of $V$ with prover $P_\psi$ when the first $t-1$, respectively $t$, calls use $I$ and the remaining calls use $R_\psi$. Then
--   $$
--   \mathbb E_\Psi\big[D(\Omega^\Psi_{t-1},\Omega^\Psi_t)\big]\le2\,\mathbb E_{\Psi,T_t}\Big[\sqrt{\langle\Psi|\rho_{t,T_t}|\Psi\rangle}\Big]\le2\sqrt{\frac{1+B\ln2}{D}} ,
--   $$
--   where $T_t$ and $\rho_{t,h}$ are as in Lemma 3. Both integrands are Haar-integrable.
--
--   Summing over the $q$ queries (telescoping) gives Eq. (3) of Theorem 4.
--
--   **Formalization Note** Query $t$ is the 0-based slot $s=t-1$. The middle expectation is written per transcript: $\|\phi_h\|^2\sqrt{\langle\psi|\rho_{t,h}|\psi\rangle}=\sqrt{\|\phi_h\|^2\,\mathrm{ov}(\psi,\phi_h)}$ for the identity-prefix branch vectors $\phi_h$ consistent with $P_\psi$.
--
--   Differences from the source:
--   - generalization: a verifier whose classical messages alternate (p.9) and whose outgoing message registers are measured in the computational basis (p.8) → a `Verifier`: any finite list of unitary steps, controlled queries, verifier messages given by any instrument $\{K_a\}$ with $\sum_a K_a^\dagger K_a=I$, and padded prover messages received through unitaries, in any order; reason: the paper's verifiers are instances (alternation is a convention that padding makes harmless, p.9; measuring a register in the computational basis is $K_a=|a\rangle\langle a|\otimes I$)
--   - encoding: private quantum registers and private measurements; controlled and uncontrolled oracle calls → pure states on $\{0,1\}\times[D]\times W$ for a finite workspace $W$ with private measurements deferred; every call controlled; reason: the paper defers private measurements (p.10) and allows controlled calls (p.8); an uncontrolled call is a controlled one with the control set to $|1\rangle$
--   - generalization: a measurable choice $\psi\mapsto P_\psi$ for $\psi\in\mathbb{CP}^{D-1}$ → a family indexed by vectors of $\mathbb C^D$ with every set $\{\psi : P_\psi(h,b)=z\}$ Borel; reason: a family on $\mathbb{CP}^{D-1}$ composed with the projection from the sphere is such a family
--   - encoding: Haar measure $\mu_D$ on pure states, equivalently on $\mathbb{CP}^{D-1}$ → `uniformSphere D`, the uniform probability measure on the unit sphere of $\mathbb C^D$; reason: every integrand depends on $\psi$ only through $|\psi\rangle\langle\psi|$, so the expectations agree
--   - generalization: the chosen maximizing provers $P_\psi$ (used throughout the hybrid) → any measurable family $\psi\mapsto P_\psi$; reason: the maximizing family is measurable (milestone `measurable_maximizer`)
--   - encoding: query $t\in[q]$, $\Omega_{t-1}$, $\Omega_t$ → slot $s=t-1<$ `numQueries V`, `hyb ψ s`, `hyb ψ (s+1)`, distance `cqDist`; reason: index shift; block-diagonal trace distance is the sum over transcripts
--   - encoding: the middle term $2\mathbb E_{\Psi,T_t}\sqrt{\langle\Psi|\rho_{t,T_t}|\Psi\rangle}$ → $2\int\sum_h[\psi\in C(h)]\sqrt{\|\phi_h\|^2\cdot\text{overlap}(\psi,\phi_h)}\,d\mu_D$ over `prefixTranscripts`; reason: $\Pr[T_t=h\mid\psi]\sqrt{\langle\psi|\rho_{t,h}|\psi\rangle}=\|\phi_h\|^2\sqrt{\text{overlap}/\|\phi_h\|^2}$ on consistent branches; before slot $t$ the hybrid $\Omega_{t-1}$ is the identity-prefix execution
--   - generalization: the bound on the two expectations → integrability of the integrand and the bound; reason: the integrand is bounded and measurable on the support of the measure; stating integrability excludes a Bochner integral that is $0$ by convention
-- source:
--   Barhoush, Quantum State Search with Classical Interactive Advice, arXiv:2610.25657 (held version, sha256 2a16939a…3408), proof of Theorem 4, third paragraph, p.13

import Mathlib
import Definitions.Def_OptimalSpectrum_Entangled_uniformSphere
import Definitions.Def_QStateSearch_Verifier
import Definitions.Def_QStateSearch_numQueries
import Definitions.Def_QStateSearch_bitsBefore
import Definitions.Def_QStateSearch_prefixTranscripts
import Definitions.Def_QStateSearch_prefixBranch
import Definitions.Def_QStateSearch_consistent
import Definitions.Def_QStateSearch_IsMeasurableProverFamily
import Definitions.Def_QStateSearch_proverBits
import Definitions.Def_QStateSearch_overlap
import Definitions.Def_QStateSearch_hyb
import Definitions.Def_QStateSearch_cqDist
open Matrix MeasureTheory OptimalSpectrum.Entangled

namespace QStateSearch

/-- **Proof of Theorem 4, hybrid step.** For a measurable prover family `ψ ↦ P_ψ`, replacing the
query at slot `t` by the identity changes the final classical–quantum state by
`E_Ψ[D(Ω^Ψ_{t−1}, Ω^Ψ_t)] ≤ 2 E_{Ψ,T_t}[√⟨Ψ|ρ_{t,T_t}|Ψ⟩] ≤ 2√((1 + B ln 2)/D)`.

Barhoush, *Quantum State Search with Classical Interactive Advice*, arXiv:2610.25657
(held version, sha256 2a16939a…3408), proof of Theorem 4, third paragraph, p.13.

**Formalization Note.** Slots are 0-based: Lean slot `s` is the paper's `t = s + 1`, and
`hyb ψ s`, `hyb ψ (s + 1)` are `Ω_{t−1}`, `Ω_t` (slots `< s`, resp. `≤ s`, use `I`; the rest `R_ψ`).
The middle term is written per transcript: `‖φ_h‖² √(⟨ψ|ρ_{t,h}|ψ⟩) = √(‖φ_h‖² · overlap ψ φ_h)`,
summed over the compatible identity-prefix branches. Integrability conjuncts rule out junk
Bochner integrals. -/
theorem hybrid_step {D : ℕ} {W : Type} [Fintype W] [DecidableEq W] (V : Verifier D W) (B : ℕ)
    (hB : proverBits V ≤ B) (P : EuclideanSpace ℂ (Fin D) → Prover)
    (hP : IsMeasurableProverFamily P) (s : ℕ) (hs : s < numQueries V) :
    Integrable (fun ψ => cqDist V (P ψ) (hyb ψ s) (hyb ψ (s + 1))) (uniformSphere D) ∧
    Integrable (fun ψ => ∑ h ∈ prefixTranscripts V.steps s [],
        if consistent (P ψ) V.steps [] h then
          Real.sqrt ((∑ x, ‖prefixBranch V.steps s V.init [] h x‖ ^ 2) *
            overlap ψ (prefixBranch V.steps s V.init [] h))
        else 0) (uniformSphere D) ∧
    ∫ ψ, cqDist V (P ψ) (hyb ψ s) (hyb ψ (s + 1)) ∂(uniformSphere D) ≤
      2 * ∫ ψ, (∑ h ∈ prefixTranscripts V.steps s [],
        if consistent (P ψ) V.steps [] h then
          Real.sqrt ((∑ x, ‖prefixBranch V.steps s V.init [] h x‖ ^ 2) *
            overlap ψ (prefixBranch V.steps s V.init [] h))
        else 0) ∂(uniformSphere D) ∧
    2 * ∫ ψ, (∑ h ∈ prefixTranscripts V.steps s [],
        if consistent (P ψ) V.steps [] h then
          Real.sqrt ((∑ x, ‖prefixBranch V.steps s V.init [] h x‖ ^ 2) *
            overlap ψ (prefixBranch V.steps s V.init [] h))
        else 0) ∂(uniformSphere D)
      ≤ 2 * Real.sqrt ((1 + B * Real.log 2) / D) := by sorry

end QStateSearch
