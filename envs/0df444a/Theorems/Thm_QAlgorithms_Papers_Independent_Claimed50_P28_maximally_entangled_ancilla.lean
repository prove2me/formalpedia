-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P28_maximally_entangled_ancilla
-- name    : QAlgorithms.Papers.Independent.Claimed50.P28.maximally_entangled_ancilla
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:26:54.461605+00:00
-- url     : https://prove2.me/theorems/ea8a398c-e8eb-43fd-9c1f-48e1235c7d72
-- title:
--   Maximally entangled auxiliary seed: unital completeness only
-- statement:
--   Let $d\ge2$, and use the maximally entangled auxiliary seed $\Psi=I/\sqrt d$ in the covariant detector, with seed $d|\Psi\rangle\!\rangle\langle\!\langle\Psi|$. Its Haar frame has
--
--   $$A=B=0.$$
--
--   It is incomplete on the full-operation and channel target spans, so those targets admit no unbiased reconstruction from this detector. It is complete on the unital target span and attains $\eta_{\mathcal U}=(d^2-1)^3+1$. This pins the source's word “generally” to the three target domains studied here. The excluded scalar case $d=1$ has no missing nontrivial sectors and all choices coincide.
-- source:
--   Optimal quantum tomography for states, measurements, and transformations, arXiv:0806.1172v1, PDF p. 4, Implementation paragraph after Fig.1

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P28

noncomputable section

open MeasureTheory

open scoped BigOperators ComplexConjugate ComplexOrder Matrix Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Claimed50.P28

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted aliases/pairing; unrelated short-name collisions are not reused.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

/-- PDF p.4: a maximally entangled auxiliary seed omits P2 and P3. For d>=2 it is
incomplete for operation and channel tomography, but attains the unital minimum. -/
theorem maximally_entangled_ancilla {d : ℕ} (hd : 2 ≤ d)
    (haar : Measure (SU d)) (hhaar : IsProbabilityHaar haar)
    (psi : EuclideanSpace ℂ (Fin d)) (hpsi : QAlgorithms.IsState psi) :
    let P := fun _ : Fin 1 => optimalSeed .unital psi
    coefficientA P = 0 ∧ coefficientB P = 0 ∧
    ¬ FrameComplete (twirledFrame haar P) .operations ∧
    ¬ FrameComplete (twirledFrame haar P) .channels ∧
    Attains haar .unital psi := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P28

end
