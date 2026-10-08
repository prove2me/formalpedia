-- Prove2me | Theorems.Thm_QuantumWalkSearch_ApproxRAA_drift_first
-- name    : QuantumWalkSearch.ApproxRAA.drift_first
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:44:05.279011+00:00
-- url     : https://prove2.me/theorems/94c01431-ce43-439c-907b-2b34e847df75
-- title:
--   §4, p. 16 — first term of Eq. (5): ‖|ν⊥ᵢ⟩ − |µ⊥ᵢ⟩‖ ≤ 2δᵢ/cos ϕᵢ ≤ 3δᵢ for i < t
-- statement:
--   Under the hypotheses of Lemma 1 with $0<\gamma\le1/40$, let $t$ be the smallest non-negative integer with $3^t\sin^{-1}\sqrt{p_M}\in[\pi/4,3\pi/4]$ and run Tolerant RAA with $T\ge t$ registers. For $i\ge1$ let $\delta_i=\||\psi_i\rangle-|\varphi_i\rangle\|$ be the distance between the state after attempt $i$ and the state Approximate RAA$(i,\gamma)$ would produce from a fresh $|\pi\rangle|0^S\rangle$, and $\sin\phi_i=\|\Pi_{\tilde M}|\varphi_i\rangle\|$. Then for every $1\le i<t$
--   $$
--   \big\||\nu_i^\perp\rangle-|\mu_i^\perp\rangle\big\|\le\frac{2\delta_i}{\cos\phi_i}\le3\delta_i .
--   $$
--
--   This bounds the first term of the error recursion (5): the leftover state after a failed measurement stays close to the normalized unmarked part of the ideal state.
-- source:
--   Magniez, Nayak, Roland, Santha, Search via Quantum Walk, arXiv:quant-ph/0608026v4, p. 16, §4, proof of Lemma 2 (first term of Eq. (5))

import Mathlib
import Definitions.Def_QuantumWalkSearch_ApproxRAA_Setting
import Definitions.Def_QuantumWalkSearch_ApproxRAA_Circuit
import Definitions.Def_QuantumWalkSearch_ApproxRAA_Tolerant

namespace QuantumWalkSearch.ApproxRAA

/-- First term of Eq. (5) (§4, p. 16, proof of Lemma 2). With `T ≥ t` registers, `t` as in
Lemma 1 and `0 < γ ≤ 1/40`, for every `1 ≤ i < t` the drift
`δ_i = ‖|ψ_i⟩ − |φ_i⟩‖` and the angle `ϕ_i = sin⁻¹ ‖Π_M̃ |φ_i⟩‖` satisfy
`‖|ν⊥_i⟩ − |µ⊥_i⟩‖ ≤ 2δ_i / cos ϕ_i ≤ 3δ_i`. -/
theorem drift_first {X : Type*} [Fintype X] [DecidableEq X] {κ : ℕ → Type*}
    [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    (M : Finset X) (piState : EuclideanSpace ℂ (X × X)) (hπ : ‖piState‖ = 1)
    (z : ∀ i, κ i) (R : ∀ i, Matrix (X × X × κ i) (X × X × κ i) ℂ)
    (γ : ℝ) (hγ : 0 < γ) (hγ' : γ ≤ 1 / 40) (hR : ApproxReflections piState z R γ) (t : ℕ)
    (ht : IsFirstHit (Real.arcsin (Real.sqrt (markedWeight M piState))) t) (T : ℕ) (htT : t ≤ T)
    (i : ℕ) (hi : 1 ≤ i) (hit : i < t) :
    ‖leftover M z R piState T i - muPerp M z R piState T i‖ ≤
        2 * ‖tolState M z R piState T i - phi M z R piState T i‖ /
          Real.cos (markedAngle M (phi M z R piState T i)) ∧
      2 * ‖tolState M z R piState T i - phi M z R piState T i‖ /
          Real.cos (markedAngle M (phi M z R piState T i)) ≤
        3 * ‖tolState M z R piState T i - phi M z R piState T i‖ := by sorry

end QuantumWalkSearch.ApproxRAA
