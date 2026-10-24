-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P01_conjugateAnti_convex
-- name    : QAlgorithms.Papers.Independent.Support50.P01.conjugateAnti_convex
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T18:23:28.117919+00:00
-- url     : https://prove2.me/theorems/e11f68d9-0c67-4874-9b24-f20d2867cacd
-- title:
--   Theorem 5: convexity of conjugate antidegradable channels
-- statement:
--   Let $A$ and $B$ have positive finite dimensions and fixed complex orthonormal bases. Let $\mathcal N_0,\mathcal N_1:A\to B$ be conjugate antidegradable CPTP maps, each with its own isometric complement and one input-independent CPTP antidegrading witness. For every $t\in[0,1]$,
--   $$t\mathcal N_0+(1-t)\mathcal N_1\text{ is conjugate antidegradable}.$$
--   This gives convexity on common input and output spaces without requiring common environment dimensions or common witnesses.
-- source:
--   Conjugate Degradability and the Quantum Capacity of Cloning Channels, arXiv:0909.3297v1, PDF p. 14, Theorem 5: convexity of conjugate antidegradable channels

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P01

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P01

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open Filter

open QAlgorithms.Papers.Independent.Information100.P67
  (receiverChannel complementaryChannel IsDegradable dilationPower maximumCoherentInformation)

open QAlgorithms.Papers.Independent.Information100.P22 (coherentInformation quantumCapacity)

open QAlgorithms.Papers.Independent.Information100.P08 (maximallyMixed)

open QAlgorithms.Papers.Independent.Dependency50.P41 (EntanglementBreaking)

open QAlgorithms.Papers.Independent.Dependency50.P40 (outputFirstChoi)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

variable {a b e c : ℕ}

/-- PDF p.14, Theorem 5: different mixture members may have different complements and witnesses. -/
theorem conjugateAnti_convex (ha : 0<a) (hb : 0<b)
    (Phi Psi : Superop (Fin a) (Fin b))
    (hPhi : ConjugateAntiChannel Phi) (hPsi : ConjugateAntiChannel Psi)
    (t : ℝ) (ht0 : 0≤t) (ht1 : t≤1) :
    ConjugateAntiChannel (fun X => (t : ℂ) • Phi X + ((1-t : ℝ) : ℂ) • Psi X) := by sorry

end QAlgorithms.Papers.Independent.Support50.P01

end
