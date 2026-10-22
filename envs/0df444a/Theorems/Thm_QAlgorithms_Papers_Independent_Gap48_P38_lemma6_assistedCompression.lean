-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P38_lemma6_assistedCompression
-- name    : QAlgorithms.Papers.Independent.Gap48.P38.lemma6_assistedCompression
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:08:09.091388+00:00
-- url     : https://prove2.me/theorems/b6059c1a-6328-482f-8bfb-1ba863eeb8e9
-- title:
--   Lemma 6: entanglement-assisted compression cannot beat dimension ratio
-- statement:
--   Let $X,Y,L,L'$ be arbitrary nonempty finite complex registers. Let $|\Psi\rangle^{LL'}$ be any unit vector, and let $\mathcal E:XL\to Y$ and $\mathcal D:YL'\to X$ be arbitrary CPTP maps. Define the attempted identity simulation by the actual composition
--
--   $$\mathcal N(\rho)=\mathcal D\bigl[(\mathcal E\otimes\operatorname{id}_{L'})(\rho\otimes\Psi)\bigr].$$
--
--   For the normalized fixed-basis maximally entangled state $|\Phi\rangle^{X'X}$, where $X'$ is a copy of $X$, its squared entanglement fidelity satisfies
--
--   $$\langle\Phi|(\operatorname{id}_{X'}\otimes\mathcal N)(\Phi)|\Phi\rangle\le\frac{|Y|}{|X|}.$$
--
--   Assistance dimensions and local channels are unrestricted. The only transmitted register is $Y$; no additional classical or backward channel is free. The statement also covers $|Y|>|X|$, when its upper bound may exceed one.
-- source:
--   Optimal quantum source coding with quantum information at the encoder and decoder, arXiv:0706.2907v2, PDF p. 9, Lemma 6: entanglement-assisted compression cannot beat dimension ratio

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P38

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Gap48.P38

/-- Lemma 6, PDF p.9, eq.(20): arbitrary finite-dimensional assistance and arbitrary
encoding/decoding CPTP maps; the fidelity is the overlap with a normalized Bell target.
No restriction |Y|<=|X| is imposed by the source. -/
theorem lemma6_assistedCompression
    (X Y L Lprime : Type) [Fintype X] [Fintype Y] [Fintype L] [Fintype Lprime]
    [DecidableEq X] [DecidableEq Y] [DecidableEq L] [DecidableEq Lprime]
    [Nonempty X] [Nonempty Y] [Nonempty L] [Nonempty Lprime]
    (psi : EuclideanSpace ℂ (L × Lprime)) (hpsi : ‖psi‖ = 1)
    (E : Superop (X × L) Y) (hE : IsChannel E)
    (D : Superop (Y × Lprime) X) (hD : IsChannel D) :
    effectProb (pureDensity (finiteMaxEntangled X))
      (idTensorSuperop (R := X) (assistedChannel E D (pureDensity psi))
        (pureDensity (finiteMaxEntangled X))) ≤ (Fintype.card Y : ℝ) / Fintype.card X := by sorry

end QAlgorithms.Papers.Independent.Gap48.P38

end
