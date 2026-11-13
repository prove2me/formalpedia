-- Prove2me | Theorems.Thm_PhaseEncodedQGE_lemma_B_19
-- name    : PhaseEncodedQGE.lemma_B_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:50:26.638202+00:00
-- url     : https://prove2.me/theorems/bc441523-f518-4780-9bdb-4dcede037ba9
-- title:
--   Lemma B.19 — phase-general flip ratio $R_i(x)=e^{i\varphi z_i}t^{z_i}\exp(i\gamma z_i\sum_{v\in N(i)}z_v)$
-- statement:
--   Let $G$ be a cubic graph and prepare every qubit in $|\chi(\theta,\varphi)\rangle=\cos(\theta/2)|0\rangle+e^{i\varphi}\sin(\theta/2)|1\rangle$; put $c=\cos(\theta/2)$, $s=\sin(\theta/2)$, $t=s/c$. With $\phi=E\phi_{\mathrm{prep}}$ the pre-mixer amplitude (one edge-phase layer), for every vertex $i$ and every outcome $x$,
--   $$R_i(x)=\frac{\phi(x\oplus e_i)}{\phi(x)}=e^{i\varphi z_i}\,t^{z_i}\exp\Bigl(i\gamma z_i\sum_{v\in N(i)}z_v\Bigr).$$
--
--   The preparation $R_X(\eta)|0\rangle$ is $|\chi(\eta,-\pi/2)\rangle$ and $|+\rangle$ is $|\chi(\pi/2,0)\rangle$, so this one formula covers both the degree-prepared members and the Hadamard member.
--
--   Differences from the source:
--   - encoding: $t=s/c$ and $R_i=\phi(x\oplus e_i)/\phi(x)$ used without comment → hypotheses $\cos(\theta/2)\ne0$ and $\sin(\theta/2)\ne0$; reason: they exclude only the angles at which t^{±1} is undefined or φ vanishes
-- source:
--   Miller, Lee, Structural Accessibility in Phase-Encoded Quantum Graph Embeddings, STOC 2027 submission (build 2026-11-03, sha256 f1132658…7c51), App. B.2.6, p.33 (PDF p.34), eq. (72) and Lemma B.19

import Mathlib
import Definitions.Def_PhaseEncodedQGE_Circuit
set_option autoImplicit false

namespace PhaseEncodedQGE

open Matrix

/-- Lemma B.19, the phase-general flip ratio (Miller, Lee, *Structural Accessibility in Phase-Encoded Quantum Graph Embeddings*, STOC 2027 submission (build 2026-11-03), App. B.2.6, p.33, eq. (72)).

For the product preparation `|χ(θ, φ)⟩^{⊗n}`, `|χ(θ, φ)⟩ = cos(θ/2)|0⟩ + e^{iφ} sin(θ/2)|1⟩`, on a
cubic graph, with `c = cos(θ/2)`, `s = sin(θ/2)`, `t = s/c`, the pre-mixer amplitude
`ϕ = E ϕ_prep` (one edge-phase layer) satisfies, for every vertex `i` and every `x`,
`R_i(x) = ϕ(x ⊕ e_i)/ϕ(x) = e^{iφ z_i} t^{z_i} exp(iγ z_i ∑_{v∈N(i)} z_v)`.
It covers `R_X(η)|0⟩ = |χ(η, −π/2)⟩` and `|+⟩ = |χ(π/2, 0)⟩`.

**Formalization Note** `c ≠ 0 ≠ s` exclude the angles at which `ϕ` vanishes and `t^{±1}` is
undefined. -/
theorem lemma_B_19 (n : ℕ) (G : SimpleGraph (Fin n)) (hG : IsCubic G) (θ φ γ : ℝ)
    (hc : Real.cos (θ / 2) ≠ 0) (hs : Real.sin (θ / 2) ≠ 0) (i : Fin n) (x : Outcome n) :
    preMixer (chiPrep n θ φ) 1 G γ (flip x i) / preMixer (chiPrep n θ φ) 1 G γ x =
      Complex.exp (Complex.I * φ * (spin x i : ℂ)) * (Real.tan (θ / 2) : ℂ) ^ (spin x i) *
        Complex.exp (Complex.I * γ * (spin x i : ℂ) * (spinSum G x i : ℂ)) := by sorry

end PhaseEncodedQGE
