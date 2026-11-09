-- Prove2me | Theorems.Thm_QStateSearch_lemma_3
-- name    : QStateSearch.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:19:27.079192+00:00
-- url     : https://prove2.me/theorems/0681d57f-c15a-4ffd-af81-861e918dff50
-- title:
--   Lemma 3 — $\mathbb E_{\Psi,T_t}\langle\Psi|\rho_{t,T_t}|\Psi\rangle\le(1+B_t\ln2)/D$
-- statement:
--   Let $V$ be a classical-message verifier, $t$ one of its query slots, and $\psi\mapsto P_\psi$ a measurable family of deterministic classical provers. In the identity-prefix execution let $\rho_{t,h}$ be the state of the oracle-input register before query $t$, conditioned on $T_t=h$. If $B_t$ padded prover bits precede this query, then
--   $$
--   \mathbb E_{\Psi,T_t}\big[\langle\Psi|\rho_{t,T_t}|\Psi\rangle\big]\le\frac{1+B_t\ln2}{D}. \tag{1}
--   $$
--   Explicitly, $\mathbb E_{T_t}\langle\psi|\rho_{t,T_t}|\psi\rangle=\sum_h[\psi\in C(h)]\,\mathrm{ov}(\psi,\phi_h)$ for the identity-prefix branch vectors $\phi_h$; this function of $\psi$ is Haar-integrable and its integral is at most $(1+B_t\ln2)/D$.
--
--   Before each query, the oracle-input register has expected overlap $O((B_t+1)/D)$ with the hidden state: classical messages reveal too little about $\psi$ to steer the query towards it.
--
--   Differences from the source:
--   - generalization: a verifier whose classical messages alternate (p.9) and whose outgoing message registers are measured in the computational basis (p.8) → a `Verifier`: any finite list of unitary steps, controlled queries, verifier messages given by any instrument $\{K_a\}$ with $\sum_a K_a^\dagger K_a=I$, and padded prover messages received through unitaries, in any order; reason: the paper's verifiers are instances (alternation is a convention that padding makes harmless, p.9; measuring a register in the computational basis is $K_a=|a\rangle\langle a|\otimes I$)
--   - encoding: private quantum registers and private measurements; controlled and uncontrolled oracle calls → pure states on $\{0,1\}\times[D]\times W$ for a finite workspace $W$ with private measurements deferred; every call controlled; reason: the paper defers private measurements (p.10) and allows controlled calls (p.8); an uncontrolled call is a controlled one with the control set to $|1\rangle$
--   - generalization: a measurable choice $\psi\mapsto P_\psi$ for $\psi\in\mathbb{CP}^{D-1}$ → a family indexed by vectors of $\mathbb C^D$ with every set $\{\psi : P_\psi(h,b)=z\}$ Borel; reason: a family on $\mathbb{CP}^{D-1}$ composed with the projection from the sphere is such a family
--   - encoding: query $t\in[q]$ (1-based) and $B_t$ → 0-based slot $t$ (the paper's query $t+1$) and `bitsBefore V.steps t`; reason: index shift only; $B_t$ is the same sum of padded lengths
--   - encoding: Haar measure $\mu_D$ on pure states, equivalently on $\mathbb{CP}^{D-1}$ → `uniformSphere D`, the uniform probability measure on the unit sphere of $\mathbb C^D$; reason: every integrand depends on $\psi$ only through $|\psi\rangle\langle\psi|$, so the expectations agree
--   - encoding: $\mathbb E_{\Psi,T_t}\langle\Psi|\rho_{t,T_t}|\Psi\rangle$ → $\int \sum_{h} [\psi\in C(h)]\,$`overlap ψ φ_h` $d\mu_D$ over `prefixTranscripts`, with $\phi_h$ the unnormalized identity-prefix branch (`prefixBranch`) and $C(h)$ given by `consistent`; reason: $\Pr[T_t=h\mid\psi]=[\psi\in C(h)]\|\phi_h\|^2$ and `overlap ψ φ_h` $=\|\phi_h\|^2\langle\psi|\rho_{t,h}|\psi\rangle$, so the sum is the conditional expectation over $T_t$
--   - generalization: the bound on $\mathbb E_{\Psi,T_t}\langle\Psi|\rho_{t,T_t}|\Psi\rangle$ → integrability of the integrand and the bound; reason: the integrand is bounded and measurable on the support of the measure; stating integrability excludes a Bochner integral that is $0$ by convention
-- source:
--   Barhoush, Quantum State Search with Classical Interactive Advice, arXiv:2610.25657 (held version, sha256 2a16939a…3408), Lemma 3, Eq. (1), p.11

import Mathlib
import Definitions.Def_OptimalSpectrum_Entangled_uniformSphere
import Definitions.Def_QStateSearch_Verifier
import Definitions.Def_QStateSearch_numQueries
import Definitions.Def_QStateSearch_bitsBefore
import Definitions.Def_QStateSearch_prefixTranscripts
import Definitions.Def_QStateSearch_prefixBranch
import Definitions.Def_QStateSearch_consistent
import Definitions.Def_QStateSearch_IsMeasurableProverFamily
import Definitions.Def_QStateSearch_overlap
open Matrix MeasureTheory OptimalSpectrum.Entangled

namespace QStateSearch

/-- **Lemma 3** (query overlap after a classical transcript). In the identity-prefix execution
with a measurable prover family `ψ ↦ P_ψ`, let `ρ_{t,h}` be the state of the oracle-input register
before query `t`, conditioned on `T_t = h`. If at most `B_t` padded prover bits precede this query,
`E_{Ψ,T_t}[⟨Ψ|ρ_{t,T_t}|Ψ⟩] ≤ (1 + B_t ln 2)/D`.

Barhoush, *Quantum State Search with Classical Interactive Advice*, arXiv:2610.25657
(held version, sha256 2a16939a…3408), Lemma 3, Eq. (1), p.11.

**Formalization Note.** For fixed `ψ`, `E_{T_t}⟨ψ|ρ_{t,T_t}|ψ⟩ = ∑_h [ψ ∈ C(h)] · overlap ψ φ_h`, with
`φ_h` the identity-prefix branch (`overlap ψ φ_h = ‖φ_h‖² ⟨ψ|ρ_{t,h}|ψ⟩`); the expectation over `Ψ`
is the integral against `uniformSphere D`. Lean slot `t` is the paper's query `t + 1`, and `B_t`
is the exact count `bitsBefore V.steps t` (a bound on it is then immediate). No condition on `D`:
Lemma 3 states none. The integrability conjunct rules out a junk Bochner integral. -/
theorem lemma_3 {D : ℕ} {W : Type} [Fintype W] [DecidableEq W] (V : Verifier D W) (t : ℕ)
    (ht : t < numQueries V) (P : EuclideanSpace ℂ (Fin D) → Prover)
    (hP : IsMeasurableProverFamily P) :
    Integrable (fun ψ => ∑ h ∈ prefixTranscripts V.steps t [],
        if consistent (P ψ) V.steps [] h then overlap ψ (prefixBranch V.steps t V.init [] h)
        else 0) (uniformSphere D) ∧
    ∫ ψ, (∑ h ∈ prefixTranscripts V.steps t [],
        if consistent (P ψ) V.steps [] h then overlap ψ (prefixBranch V.steps t V.init [] h)
        else 0) ∂(uniformSphere D)
      ≤ (1 + bitsBefore V.steps t * Real.log 2) / D := by sorry

end QStateSearch
