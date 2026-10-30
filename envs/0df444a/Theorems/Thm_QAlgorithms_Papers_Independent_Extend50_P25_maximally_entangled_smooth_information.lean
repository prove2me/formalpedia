-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P25_maximally_entangled_smooth_information
-- name    : QAlgorithms.Papers.Independent.Extend50.P25.maximally_entangled_smooth_information
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:27:48.700362+00:00
-- url     : https://prove2.me/theorems/c34ea1e3-93c8-4da8-904b-cb1dbd0dc74a
-- title:
--   Lemma 7.1: smooth max-mutual information of a maximally entangled state
-- statement:
--   Let $d\ge1$, $0\le\epsilon<1$, and $|\phi^+\rangle=d^{-1/2}\sum_{i=0}^{d-1}|ii\rangle$. Define $I_{\max}^\epsilon(A:B)$ by minimizing over positive subnormalized states within purified distance $\epsilon$, with $D_{\max}(\rho\|\rho_A\otimes\sigma_B)$ minimized over normalized $\sigma_B$. All logarithms have base 2. Then
--   $$2\log_2\bigl(d(1-\epsilon^2)\bigr)\le I_{\max}^\epsilon(A:B)_{\phi^+}\le2\log_2\left\lceil d(1-\epsilon^2)\right\rceil.$$
--   This bounds the smoothed communication-relevant information of a maximally entangled state. The formal definition uses extended-real infima to preserve empty and unbounded optimization behavior.
-- source:
--   Asymptotic performance of port-based teleportation, arXiv:1809.10751v2, PDF p. 48, Lemma 7.1: smooth max-mutual information of a maximally entangled state

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P25

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P25

open QAlgorithms MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open scoped BigOperators ComplexConjugate Matrix ComplexOrder

/-- Lemma 7.1, PDF p.48: smooth max-mutual information of phi+ in BITS.
The upper ceiling is INSIDE the logarithm; eps<1 excludes log zero and the zero state. -/
theorem maximally_entangled_smooth_information (d : ℕ) (hd : 1 ≤ d)
    (eps : ℝ) (heps0 : 0 ≤ eps) (heps1 : eps < 1) :
    (2 * Real.logb 2 ((d : ℝ)*(1-eps^2)) : EReal) ≤ smoothMaxInformation d eps ∧
    smoothMaxInformation d eps ≤
      (2 * Real.logb 2 (Nat.ceil ((d : ℝ)*(1-eps^2)) : ℝ) : EReal) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P25

end
