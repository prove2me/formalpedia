-- Prove2me | Theorems.Thm_QuantumWalkSearch_ApproxRAA_drift_third
-- name    : QuantumWalkSearch.ApproxRAA.drift_third
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:44:10.646986+00:00
-- url     : https://prove2.me/theorems/b7390f44-3aa1-4190-9986-a9c85fcb9a2c
-- title:
--   §4, p. 16 — last term of Eq. (5): ‖|µ⊥₀⟩ − |φ₀⟩‖ = √(2 − 2cos ϕ₀) = 2 sin(ϕ₀/2) ≤ ϕ₀
-- statement:
--   Let $|\pi\rangle$ be a unit vector with $p_M=\|\Pi_M|\pi\rangle\|^2<1$, $|\varphi_0\rangle=|\pi\rangle|0^S\rangle$, $\phi_0=\sin^{-1}\sqrt{p_M}$ and $|\mu_0^\perp\rangle=(\mathrm{Id}-\Pi_{\tilde M})|\varphi_0\rangle/\|(\mathrm{Id}-\Pi_{\tilde M})|\varphi_0\rangle\|$. Then
--   $$
--   \big\||\mu_0^\perp\rangle-|\varphi_0\rangle\big\|=\sqrt{2-2\cos\phi_0}=2\sin(\phi_0/2)\le\phi_0 .
--   $$
--
--   This is the last term of the error recursion (5), the distance between the initial state and its normalized unmarked part.
--
--   **Formalization Note** The hypothesis $p_M<1$ excludes the case in which $|\varphi_0\rangle$ is entirely marked and $|\mu_0^\perp\rangle$ is undefined; in the proof of Lemma 2 the paper has $p_M<1/2$.
-- source:
--   Magniez, Nayak, Roland, Santha, Search via Quantum Walk, arXiv:quant-ph/0608026v4, p. 16, §4, proof of Lemma 2 (last term of Eq. (5))

import Mathlib
import Definitions.Def_QuantumWalkSearch_ApproxRAA_Setting
import Definitions.Def_QuantumWalkSearch_ApproxRAA_Circuit
import Definitions.Def_QuantumWalkSearch_ApproxRAA_Tolerant

namespace QuantumWalkSearch.ApproxRAA

/-- Last term of Eq. (5) (§4, p. 16, proof of Lemma 2). With `ϕ₀ = sin⁻¹ √p_M` and
`p_M < 1`: `‖|µ⊥_0⟩ − |φ₀⟩‖ = √(2 − 2 cos ϕ₀) = 2 sin(ϕ₀/2) ≤ ϕ₀`. -/
theorem drift_third {X : Type*} [Fintype X] [DecidableEq X] {κ : ℕ → Type*}
    [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    (M : Finset X) (piState : EuclideanSpace ℂ (X × X)) (hπ : ‖piState‖ = 1)
    (z : ∀ i, κ i) (R : ∀ i, Matrix (X × X × κ i) (X × X × κ i) ℂ)
    (hpM : markedWeight M piState < 1) (T : ℕ) :
    ‖muPerp M z R piState T 0 - phi M z R piState T 0‖ =
        Real.sqrt (2 - 2 * Real.cos (Real.arcsin (Real.sqrt (markedWeight M piState)))) ∧
      Real.sqrt (2 - 2 * Real.cos (Real.arcsin (Real.sqrt (markedWeight M piState)))) =
        2 * Real.sin (Real.arcsin (Real.sqrt (markedWeight M piState)) / 2) ∧
      2 * Real.sin (Real.arcsin (Real.sqrt (markedWeight M piState)) / 2) ≤
        Real.arcsin (Real.sqrt (markedWeight M piState)) := by sorry

end QuantumWalkSearch.ApproxRAA
