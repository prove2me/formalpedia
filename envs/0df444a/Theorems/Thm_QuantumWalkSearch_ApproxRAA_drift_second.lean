-- Prove2me | Theorems.Thm_QuantumWalkSearch_ApproxRAA_drift_second
-- name    : QuantumWalkSearch.ApproxRAA.drift_second
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:46:06.016987+00:00
-- url     : https://prove2.me/theorems/30a57946-cdfb-4337-94ec-ac66216030fe
-- title:
--   §4, p. 16 — second term of Eq. (5): ‖|µ⊥_{k+1}⟩ − |µ⊥_k⟩‖ ≤ 2‖ω_{k+1}‖/cos ϕ_{k+1} ≤ 12β_{k+1}3^kϕ₀ for k < t − 1
-- statement:
--   Under the hypotheses of Lemma 1 with $0<\gamma\le1/40$, let $t$ be the smallest non-negative integer with $3^t\phi_0\in[\pi/4,3\pi/4]$, where $\phi_0=\sin^{-1}\sqrt{p_M}$. Let $|\omega_{k+1}\rangle=E_{k+1}\cdot\mathrm{ref}(\tilde{\mathcal M}^\perp)|\varphi_k\rangle$ be the error state of level $k+1$ and $\sin\phi_{k+1}=\|\Pi_{\tilde M}|\varphi_{k+1}\rangle\|$. Then for every $k<t-1$
--   $$
--   \big\||\mu^\perp_{k+1}\rangle-|\mu^\perp_k\rangle\big\|\le\frac{2\|\omega_{k+1}\|}{\cos\phi_{k+1}}\le12\,\beta_{k+1}\,3^k\phi_0 .
--   $$
--
--   This bounds the middle terms of the error recursion (5): the unmarked direction of the ideal states drifts by at most $12\beta_{k+1}\bar\phi_k$ per level.
-- source:
--   Magniez, Nayak, Roland, Santha, Search via Quantum Walk, arXiv:quant-ph/0608026v4, p. 16, §4, proof of Lemma 2 (second term of Eq. (5)); ω_{k+1} defined p. 13

import Mathlib
import Definitions.Def_QuantumWalkSearch_ApproxRAA_Setting
import Definitions.Def_QuantumWalkSearch_ApproxRAA_Circuit
import Definitions.Def_QuantumWalkSearch_ApproxRAA_Tolerant

namespace QuantumWalkSearch.ApproxRAA

/-- Second term of Eq. (5) (§4, p. 16, proof of Lemma 2). With `t` as in Lemma 1,
`0 < γ ≤ 1/40`, `ϕ₀ = sin⁻¹ √p_M` and the error state
`|ω_{k+1}⟩ = E_{k+1} · ref(M̃⊥) |φ_k⟩` (p. 13), for every `k < t − 1` (here `k : Fin T`):
`‖|µ⊥_{k+1}⟩ − |µ⊥_k⟩‖ ≤ 2‖ω_{k+1}‖ / cos ϕ_{k+1} ≤ 12 β_{k+1} 3^k ϕ₀`. -/
theorem drift_second {X : Type*} [Fintype X] [DecidableEq X] {κ : ℕ → Type*}
    [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    (M : Finset X) (piState : EuclideanSpace ℂ (X × X)) (hπ : ‖piState‖ = 1)
    (z : ∀ i, κ i) (R : ∀ i, Matrix (X × X × κ i) (X × X × κ i) ℂ)
    (γ : ℝ) (hγ : 0 < γ) (hγ' : γ ≤ 1 / 40) (hR : ApproxReflections piState z R γ) (t : ℕ)
    (ht : IsFirstHit (Real.arcsin (Real.sqrt (markedWeight M piState))) t) (T : ℕ)
    (k : Fin T) (hkt : k.val + 1 < t) :
    ‖muPerp M z R piState T (k.val + 1) - muPerp M z R piState T k.val‖ ≤
        2 * ‖act (errOp M z R piState T k) (act (flipMarked M) (phi M z R piState T k.val))‖ /
          Real.cos (markedAngle M (phi M z R piState T (k.val + 1))) ∧
      2 * ‖act (errOp M z R piState T k) (act (flipMarked M) (phi M z R piState T k.val))‖ /
          Real.cos (markedAngle M (phi M z R piState T (k.val + 1))) ≤
        12 * beta γ (k.val + 1) *
          ((3 : ℝ) ^ k.val * Real.arcsin (Real.sqrt (markedWeight M piState))) := by sorry

end QuantumWalkSearch.ApproxRAA
