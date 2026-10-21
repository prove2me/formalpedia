-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P28_bell_realization
-- name    : QAlgorithms.Papers.Independent.Claimed50.P28.bell_realization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:24:32.916302+00:00
-- url     : https://prove2.me/theorems/aec817f3-847c-465a-ad93-b7468084b6da
-- title:
--   Two-Bell randomized realization with the physical normalization
-- statement:
--   Let $d\ge1$ and choose any of the attaining square-root matrices $\Psi$ above. The auxiliary pair is the normalized state $|\Psi\rangle\!\rangle$, and the separate channel input is $|I\rangle\!\rangle/\sqrt d$. Apply independent Haar $U,V\in SU(d)$ to the two system wires. Let $B_j$ be the shift-and-phase unitary Bell matrices, with normalized Bell vectors $|B_j\rangle\!\rangle/\sqrt d$. For the two Bell labels $j,k$, define
--
--   $$t^{j,k}_{x,y}=\frac1d\sum_{a,b,s,t}\Psi_{ab}\overline{(B_j)_{as}}U_{sx}\overline{(B_k)_{bt}}V_{ty},\qquad E_{j,k}[(x,y),(x',y')]=\overline{t^{j,k}_{x,y}}t^{j,k}_{x',y'}.$$
--
--   For every $U,V$, these effects are positive and sum to the identity. There are known Haar-measure-preserving relabellings $r_{j,k}$ of $SU(d)^2$, absorbing Bell labels and the fixed conjugation transport, for which
--
--   $$E_{j,k}(U,V)=d^{-4}\,[d\Pi_{r_{j,k}(U,V)}].$$
--
--   There are $d^4$ label pairs. Hence this randomized discrete measurement realizes the continuous physical density $d\Pi$, whose induced tester under the separate maximally entangled channel input is exactly $\Pi$. No foreign equation locator is used.
-- source:
--   Optimal quantum tomography for states, measurements, and transformations, arXiv:0806.1172v1, PDF p. 4, Fig.1 and implementation paragraph

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P28

noncomputable section

open MeasureTheory

open scoped BigOperators ComplexConjugate ComplexOrder Matrix Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Claimed50.P28

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted aliases/pairing; unrelated short-name collisions are not reused.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

/-- PDF pp.3–4, Fig.1: two Bell measurements with random unitaries implement d Pi.
Known Bell labels and fixed conjugation transports are included in a Haar-preserving relabelling.
The factor d^(-4) belongs to each of d^4 discrete Bell-label pairs.
For channels the printed beta=[(d-1)(2+sqrt(2)(d²-1))]^(-1/2) is replaced by
sqrt((d+1)/(2+sqrt(2)(d²-1))); this is the minimal correction fixed by
A=beta²/(d+1) in (29),(36) and the channel optimizer in (33). -/
theorem bell_realization {d : ℕ} (hd : 0 < d)
    (haar : Measure (SU d)) (hhaar : IsProbabilityHaar haar)
    (K : TomographyDomain) (psi : EuclideanSpace ℂ (Fin d)) (hpsi : QAlgorithms.IsState psi) :
    let Psi := seedMatrix K psi
    QAlgorithms.IsDensityMatrix (operatorDyad Psi) ∧
    QAlgorithms.IsDensityMatrix (maximallyEntangledDensity d) ∧
    (∀ g, (∀ j k, (bellEffect Psi g j k).PosSemidef) ∧
      ∑ j, ∑ k, bellEffect Psi g j k = 1) ∧
    ∃ relabel : (Fin d × Fin d) → (Fin d × Fin d) → GroupPair d → GroupPair d,
      (∀ j k, MeasurePreserving (relabel j k) (haar.prod haar) (haar.prod haar)) ∧
      (∀ j k g, bellEffect Psi g j k = ((d : ℂ)^4)⁻¹ •
        ((d : ℂ) • testerSeedOrbit (optimalSeed K psi) (relabel j k g))) ∧
      (∀ g, inducedTester (maximallyEntangledDensity d)
        ((d : ℂ) • testerSeedOrbit (optimalSeed K psi) g) = testerSeedOrbit (optimalSeed K psi) g) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P28

end
