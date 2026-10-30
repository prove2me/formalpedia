-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P14_two_ancilla_universality
-- name    : QAlgorithms.Papers.Independent.Extend50.P14.two_ancilla_universality
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:15:39.656645+00:00
-- url     : https://prove2.me/theorems/bc6922cc-175f-459c-968a-198f4e00a2ae
-- title:
--   Corollary 16: two ancillas remove system interactions
-- statement:
--   For n,d≥1 and ΔE>0 use the same identical equally spaced system energies as Theorem 15 and two ground-state ancilla qubits of gap ΔE. Every energy-conserving unitary V admits a finite-product W using only system/ancilla transfers R_{j,a}^{(l)}, R_{j,b}^{(l)} and local Z_a,Z_b, such that
--
--   $$W(|\psi\rangle|0\rangle_a|0\rangle_b)=(V|\psi\rangle)|0\rangle_a|0\rangle_b\quad\text{for all }\psi.$$
--
--   The same W is reachable with finite pulses in the drift-containing G27 model. There are no direct system/system interactions. Z_b is included as required by G22–G23 and G27, correcting the repeated entry in G26.
-- source:
--   Restrictions on realizable unitary operations imposed by symmetry and locality, arXiv:2003.05524v3, PDF p. 46, Corollary 16: two ancillas eliminate direct system-system interactions

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P14

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P14

open scoped Classical Matrix ComplexConjugate Matrix.Norms.Frobenius

open MeasureTheory

-- Exact accepted aliases and physical operators, without local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Advance50.P49 (onWire multiSwap)

attribute [local instance 100] LieRing.ofAssociativeRing

/-- PDF p.46, Corollary 16/G29: both ancillas return exactly, with no system
interactions or measurement. G26's duplicated entry is corrected to Z_b as in G27. -/
theorem two_ancilla_universality (n d : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d)
    (gap : ℝ) (hGap : 0 < gap) (V : EMat n d)
    (hV : V ∈ Matrix.unitaryGroup (EnergyBasis n d) ℂ)
    (hComm : V * intrinsicEnergy n d gap = intrinsicEnergy n d gap * V) :
    ∃ W : Mat ((EnergyBasis n d × Bool) × Bool), W ∈ controlGenerated (twoAncillaControls n d) ∧
      (∀ psi : EuclideanSpace ℂ (EnergyBasis n d),
        act W (groundEmbed (groundEmbed psi)) = groundEmbed (groundEmbed (act V psi))) ∧
      PulseReachable (twoAncillaDrift n d gap) (twoAncillaControls n d) W := by sorry

end QAlgorithms.Papers.Independent.Extend50.P14

end
