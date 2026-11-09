-- Prove2me | Theorems.Thm_QStateSearch_eq_2
-- name    : QStateSearch.eq_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:19:45.888727+00:00
-- url     : https://prove2.me/theorems/856fdc08-0563-4c03-badd-ff934dcfac8e
-- title:
--   Eq. (2) — $\mathbb E[\ln(1/\mu_D(C(T_t)))]\le B_t\ln2$
-- statement:
--   Let $V$ be a classical-message verifier, $t$ one of its query slots, and $\psi\mapsto P_\psi$ a measurable family of deterministic classical provers. In the identity-prefix execution ($\Psi\leftarrow\mu_D$, prover $P_\Psi$, every oracle call before slot $t$ replaced by $I$), let $T_t$ be the public transcript immediately before slot $t$ and $C(h)=\{\psi : P_\psi\text{ is consistent with }h\}$. Then
--   $$
--   \mathbb E\Big[\ln\frac1{\mu_D(C(T_t))}\Big]\le B_t\ln2 ,
--   $$
--   where $B_t$ is the number of padded prover bits before slot $t$. Explicitly, with $\phi_h$ the identity-prefix branch vector, $\Pr[T_t=h]=\mu_D(C(h))\,\|\phi_h\|^2$ and
--   $$
--   \sum_h\|\phi_h\|^2\,\mu_D(C(h))\ln\frac1{\mu_D(C(h))}\le B_t\ln2 .
--   $$
--
--   The transcript before a query carries at most $B_t\ln 2$ nats of information about the hidden state, however the verifier's messages are chosen.
--
--   Differences from the source:
--   - generalization: a verifier whose classical messages alternate (p.9) and whose outgoing message registers are measured in the computational basis (p.8) → a `Verifier`: any finite list of unitary steps, controlled queries, verifier messages given by any instrument $\{K_a\}$ with $\sum_a K_a^\dagger K_a=I$, and padded prover messages received through unitaries, in any order; reason: the paper's verifiers are instances (alternation is a convention that padding makes harmless, p.9; measuring a register in the computational basis is $K_a=|a\rangle\langle a|\otimes I$)
--   - encoding: private quantum registers and private measurements; controlled and uncontrolled oracle calls → pure states on $\{0,1\}\times[D]\times W$ for a finite workspace $W$ with private measurements deferred; every call controlled; reason: the paper defers private measurements (p.10) and allows controlled calls (p.8); an uncontrolled call is a controlled one with the control set to $|1\rangle$
--   - generalization: a measurable choice $\psi\mapsto P_\psi$ for $\psi\in\mathbb{CP}^{D-1}$ → a family indexed by vectors of $\mathbb C^D$ with every set $\{\psi : P_\psi(h,b)=z\}$ Borel; reason: a family on $\mathbb{CP}^{D-1}$ composed with the projection from the sphere is such a family
--   - encoding: query $t\in[q]$ (1-based) and $B_t$ → 0-based slot $t$ (the paper's query $t+1$) and `bitsBefore V.steps t`; reason: index shift only; $B_t$ is the same sum of padded lengths
--   - encoding: the expectation over $T_t$ → the finite sum over `prefixTranscripts` with weights $\mu_D(C(h))\|\phi_h\|^2$; a null $C(h)$ contributes $0$; reason: this is the law of $T_t$; the paper's expectation is over positive-probability transcripts
-- source:
--   Barhoush, Quantum State Search with Classical Interactive Advice, arXiv:2610.25657 (held version, sha256 2a16939a…3408), proof of Lemma 3, Eq. (2), p.12

import Mathlib
import Definitions.Def_OptimalSpectrum_Entangled_uniformSphere
import Definitions.Def_QStateSearch_Verifier
import Definitions.Def_QStateSearch_numQueries
import Definitions.Def_QStateSearch_bitsBefore
import Definitions.Def_QStateSearch_prefixTranscripts
import Definitions.Def_QStateSearch_prefixBranch
import Definitions.Def_QStateSearch_consistent
import Definitions.Def_QStateSearch_IsMeasurableProverFamily
open Matrix MeasureTheory OptimalSpectrum.Entangled

namespace QStateSearch

/-- **Eq. (2).** In the identity-prefix execution with a measurable prover family `ψ ↦ P_ψ` and
`Ψ ← μ_D`, the transcript `T_t` before query slot `t` satisfies
`E[ln(1/μ_D(C(T_t)))] ≤ B_t ln 2`.

Barhoush, *Quantum State Search with Classical Interactive Advice*, arXiv:2610.25657
(held version, sha256 2a16939a…3408), proof of Lemma 3, Eq. (2), p.12.

**Formalization Note.** The probability of transcript `h` in the identity-prefix execution is
`μ_D(C(h)) · ‖φ_h‖²`, where `φ_h = prefixBranch … h` is the identity-prefix branch vector and
`C(h) = {ψ | consistent (P ψ) V.steps [] h}` is the compatible set; the expectation is the finite
sum over `prefixTranscripts`. Lean slot `t` (0-based) is the paper's query `t + 1`, and `B_t` is
`bitsBefore V.steps t`. A null `C(h)` contributes `0`, as in the paper ("positive-probability
transcript"). -/
theorem eq_2 {D : ℕ} {W : Type} [Fintype W] [DecidableEq W] (V : Verifier D W) (t : ℕ)
    (ht : t < numQueries V) (P : EuclideanSpace ℂ (Fin D) → Prover)
    (hP : IsMeasurableProverFamily P) :
    ∑ h ∈ prefixTranscripts V.steps t [],
        (∑ x, ‖prefixBranch V.steps t V.init [] h x‖ ^ 2) *
          ((uniformSphere D {ψ | consistent (P ψ) V.steps [] h}).toReal *
            Real.log (1 / (uniformSphere D {ψ | consistent (P ψ) V.steps [] h}).toReal))
      ≤ bitsBefore V.steps t * Real.log 2 := by sorry

end QStateSearch
