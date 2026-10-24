-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P01_conjugateAnti_postprocess
-- name    : QAlgorithms.Papers.Independent.Support50.P01.conjugateAnti_postprocess
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T18:22:53.560388+00:00
-- url     : https://prove2.me/theorems/cd6ced58-a5ff-4bb5-b24e-bf132fe3cf9f
-- title:
--   Lemma 2: closure under CPTP postprocessing
-- statement:
--   Let $A,B,C$ be positive finite-dimensional complex spaces with fixed bases. Suppose $\mathcal N:A\to B$ is a conjugate antidegradable channel: it has a common isometric dilation and complement $\mathcal N^c$ and one CPTP map $D_a$ satisfying $D_a\mathcal N^c=T\mathcal N$ on every operator. For any CPTP map $\Delta:B\to C$,
--   $$\Delta\circ\mathcal N\text{ is conjugate antidegradable}.$$
--   The conclusion allows the complement of the composed dilation and a new CPTP witness. No unitality or inverse-channel assumption is imposed.
-- source:
--   Conjugate Degradability and the Quantum Capacity of Cloning Channels, arXiv:0909.3297v1, PDF p. 13, Lemma 2: closure under CPTP postprocessing

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

/-- PDF pp.13–14, Lemma 2: postprocessing by any CPTP map; no unitality condition.
The proof's Eq.(36) reverses Kraus order; trace preservation uses sum E_k†E_k=I. -/
theorem conjugateAnti_postprocess (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (Phi : Superop (Fin a) (Fin b)) (Delta : Superop (Fin b) (Fin c))
    (hPhi : ConjugateAntiChannel Phi) (hDelta : IsChannel Delta) :
    ConjugateAntiChannel (Delta ∘ Phi) := by sorry

end QAlgorithms.Papers.Independent.Support50.P01

end
