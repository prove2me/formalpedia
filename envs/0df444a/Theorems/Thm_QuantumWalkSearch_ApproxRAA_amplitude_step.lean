-- Prove2me | Theorems.Thm_QuantumWalkSearch_ApproxRAA_amplitude_step
-- name    : QuantumWalkSearch.ApproxRAA.amplitude_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:43:00.346531+00:00
-- url     : https://prove2.me/theorems/7d313364-5ef5-457e-b583-7da348365ede
-- title:
--   §4, p. 13 — one level of Approximate RAA: |sin ϕ_{i+1} − sin 3ϕᵢ| ≤ β_{i+1}|sin 2ϕᵢ|
-- statement:
--   Under the hypotheses of Fact 1 (in particular $\gamma>0$), let $\phi_i\in[0,\pi/2]$ be the angle of $|\varphi_i\rangle=A_i|\pi\rangle|0^S\rangle$ with the unmarked subspace, $\sin\phi_i=\|\Pi_{\tilde M}|\varphi_i\rangle\|$. For every $0\le i<T$ with $\phi_i\le\pi/3$,
--   $$
--   \big|\sin\phi_{i+1}-\sin 3\phi_i\big|\le\beta_{i+1}\,\big|\sin 2\phi_i\big| .
--   $$
--
--   One level of exact amplitude amplification triples the angle; the bound says that replacing $\mathrm{ref}(\pi)$ by $R_{i+1}$ perturbs the marked amplitude by at most $\beta_{i+1}|\sin2\phi_i|$. Iterating it is the error analysis of Lemma 1.
--
--   **Formalization Note** The paper compares the marked amplitude of $\sin3\phi_i|\mu_i\rangle+\cos3\phi_i|\mu_i^\perp\rangle+|\omega_{i+1}\rangle$ with $\sin 3\phi_i$, which requires $\sin3\phi_i\ge0$; the hypothesis $\phi_i\le\pi/3$ makes this explicit. In the proof of Lemma 1 it holds for every level used.
-- source:
--   Magniez, Nayak, Roland, Santha, Search via Quantum Walk, arXiv:quant-ph/0608026v4, p. 13, §4, display after Eq. (3) (proof of Lemma 1)

import Mathlib
import Definitions.Def_QuantumWalkSearch_ApproxRAA_Setting
import Definitions.Def_QuantumWalkSearch_ApproxRAA_Circuit

namespace QuantumWalkSearch.ApproxRAA

/-- The one-level amplitude bound (§4, p. 13, display after Eq. (3)). With
`ϕ_i = sin⁻¹ ‖Π_M̃ |φ_i⟩‖`, for `γ > 0`, `i = ii < T` and `ϕ_i ≤ π/3`:
`|sin ϕ_{i+1} − sin 3ϕ_i| ≤ β_{i+1} |sin 2ϕ_i|`. -/
theorem amplitude_step {X : Type*} [Fintype X] [DecidableEq X] {κ : ℕ → Type*}
    [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    (M : Finset X) (piState : EuclideanSpace ℂ (X × X)) (hπ : ‖piState‖ = 1)
    (z : ∀ i, κ i) (R : ∀ i, Matrix (X × X × κ i) (X × X × κ i) ℂ) (γ : ℝ) (hγ : 0 < γ)
    (hR : ApproxReflections piState z R γ) (T : ℕ) (ii : Fin T)
    (hangle : markedAngle M (phi M z R piState T ii.val) ≤ Real.pi / 3) :
    |Real.sin (markedAngle M (phi M z R piState T (ii.val + 1))) -
        Real.sin (3 * markedAngle M (phi M z R piState T ii.val))| ≤
      beta γ (ii.val + 1) * |Real.sin (2 * markedAngle M (phi M z R piState T ii.val))| := by sorry

end QuantumWalkSearch.ApproxRAA
