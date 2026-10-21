-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P46_fourierErasure
-- name    : QAlgorithms.Papers.Independent.Next46.P46.fourierErasure
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T15:04:52.308495+00:00
-- url     : https://prove2.me/theorems/8034dfde-f168-41f8-9990-cd640196880a
-- title:
--   Fourier measurement and feed-forward erase the duplicated label
-- statement:
--   Let $M,S>0$ and let each $|\phi_{ms}\rangle$ be a unit vector in a finite residual register $H$, without an orthogonality requirement. Start with the ideal duplicated-label state
--
--   $$
--   |\Omega\rangle=\frac1{\sqrt{MS}}\sum_{m,s}|m,s\rangle^A|m,s\rangle^B|\phi_{ms}\rangle.
--   $$
--
--   Use residues $s,t=0,\ldots,S-1$ and measure Alice's $s$ label in the basis $|\hat t\rangle=S^{-1/2}\sum_s e^{2\pi i st/S}|s\rangle$. If $b_t$ is the unnormalized remaining branch, then
--
--   $$
--   \|b_t\|^2=\frac1S,\qquad
--   D_tb_t=\frac1{\sqrt S}|\Xi\rangle,\qquad
--   |\Xi\rangle=\frac1{\sqrt{MS}}\sum_{m,s}|m\rangle^A|m,s\rangle^B|\phi_{ms}\rangle,
--   $$
--
--   where $D_t$ applies the positive phase $e^{2\pi i st/S}$ on Bob's $s$ label. The vector $\Xi$ is normalized and the sum of the corrected subnormalized branch density matrices is $|\Xi\rangle\!\langle\Xi|$.
--
--   This is the finite ideal-state erasure identity. It does not give exact transcript uniformity for approximate real inputs or for the preceding first message.
-- source:
--   Relating quantum privacy and quantum coherence: an operational approach, arXiv:quant-ph/0307053v1, PDF p. 4, Fourier erasure step following the analogue of (5)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P46

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P46

open QAlgorithms

open scoped Matrix ComplexConjugate

attribute [local instance] Classical.decEq Classical.propDecidable

-- The repair request explicitly authorizes imports from the pinned accepted papers.

open QAlgorithms.Papers.Independent.Information100.P21 (Vec Op)

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Information100.P22 (bell)

open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)

open QAlgorithms.Papers.Independent.Frontier30.P12
  (coherentInfo quantumMutualInfo mutualAE marginalAE triCopies EntProtocol RectangularKrausData)

open QAlgorithms.Papers.Independent.Dependency50.P19 (channelSource)

open QAlgorithms.Papers.Independent.Dependency50.P48 (IsDilation)

/-- arXiv:quant-ph/0307053v1, PDF p.4: Fourier erasure on the displayed ideal state.
Each outcome has probability 1/S; after feed-forward every normalized branch is (5).
Residual vectors need only have unit norm, since the m,s labels are orthogonal. -/
theorem fourierErasure {H : Type} [Fintype H] [Nonempty H] {m s : ℕ}
    (hm : 0 < m) (hs : 0 < s) (phi : Fin m → Fin s → Vec H)
    (hphi : ∀ a b, IsState (phi a b)) :
    IsState (erasedVector phi) ∧
    (∀ t : Fin s, ‖fourierBranch phi t‖ ^ 2 = (s : ℝ)⁻¹ ∧
      correctedBranch phi t = ((Real.sqrt (s : ℝ))⁻¹ : ℂ) • erasedVector phi) ∧
    (∑ t : Fin s, pureDensity (correctedBranch phi t)) =
      pureDensity (erasedVector phi) := by sorry

end QAlgorithms.Papers.Independent.Next46.P46

end
