-- Prove2me | Theorems.Thm_QuantumWalkSearch_ApproxRAA_drift_total
-- name    : QuantumWalkSearch.ApproxRAA.drift_total
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:44:18.427957+00:00
-- url     : https://prove2.me/theorems/180ad43d-41bb-44b4-9fe4-2d8da5f572f8
-- title:
--   §4, p. 16 — the accumulated error of Tolerant RAA: δ_t ≤ π/8 + 9γ/8
-- statement:
--   Under the hypotheses of Lemma 1 with $0<\gamma\le1/40$, let $t$ be the smallest non-negative integer with $3^t\sin^{-1}\sqrt{p_M}\in[\pi/4,3\pi/4]$, and run Tolerant RAA with $T\ge t$ registers. Let $|\psi_t\rangle=A_t|\nu^\perp_{t-1}\rangle$ be the state after Step 4 of attempt $t$ and $|\varphi_t\rangle=A_t|\pi\rangle|0^S\rangle$. Then
--   $$
--   \delta_t=\big\||\psi_t\rangle-|\varphi_t\rangle\big\|\le\frac\pi8+\frac{9\gamma}8 .
--   $$
--
--   Re-using the leftover state of a failed attempt instead of a fresh copy of $|\pi\rangle|0^S\rangle$ costs at most this much at the decisive attempt $t$; combined with Lemma 1 it leaves a marked projection of length at least $1/\sqrt{12}-3\gamma$.
--
--   **Formalization Note** The paper states this under $p_M<1/2$, which makes $t\ge1$. The Lean statement does not assume it: when $p_M\ge1/2$ one has $t=0$ and $|\psi_0\rangle=|\varphi_0\rangle$, so the bound holds trivially. At $t=0$ the formula $A_t|\nu^\perp_{t-1}\rangle$ reads $|\varphi_0\rangle$.
-- source:
--   Magniez, Nayak, Roland, Santha, Search via Quantum Walk, arXiv:quant-ph/0608026v4, p. 16, §4, proof of Lemma 2 (last line of the display after Eq. (5))

import Mathlib
import Definitions.Def_QuantumWalkSearch_ApproxRAA_Setting
import Definitions.Def_QuantumWalkSearch_ApproxRAA_Circuit
import Definitions.Def_QuantumWalkSearch_ApproxRAA_Tolerant

namespace QuantumWalkSearch.ApproxRAA

/-- The accumulated error (§4, p. 16, proof of Lemma 2). With `T ≥ t` registers, `t` as in
Lemma 1 and `0 < γ ≤ 1/40`, the drift at attempt `t` of Tolerant RAA satisfies
`δ_t = ‖|ψ_t⟩ − |φ_t⟩‖ ≤ π/8 + 9γ/8`. -/
theorem drift_total {X : Type*} [Fintype X] [DecidableEq X] {κ : ℕ → Type*}
    [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    (M : Finset X) (piState : EuclideanSpace ℂ (X × X)) (hπ : ‖piState‖ = 1)
    (z : ∀ i, κ i) (R : ∀ i, Matrix (X × X × κ i) (X × X × κ i) ℂ)
    (γ : ℝ) (hγ : 0 < γ) (hγ' : γ ≤ 1 / 40) (hR : ApproxReflections piState z R γ) (t : ℕ)
    (ht : IsFirstHit (Real.arcsin (Real.sqrt (markedWeight M piState))) t) (T : ℕ)
    (htT : t ≤ T) :
    ‖tolState M z R piState T t - phi M z R piState T t‖ ≤ Real.pi / 8 + 9 * γ / 8 := by sorry

end QuantumWalkSearch.ApproxRAA
