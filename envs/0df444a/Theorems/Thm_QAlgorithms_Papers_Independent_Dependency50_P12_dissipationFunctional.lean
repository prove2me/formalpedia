-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P12_dissipationFunctional
-- name    : QAlgorithms.Papers.Independent.Dependency50.P12.dissipationFunctional
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T13:45:04.372745+00:00
-- url     : https://prove2.me/theorems/109f9f80-72e8-4b08-a635-4d5734d6196d
-- title:
--   Lemma 2.16: dissipation functional and normalizations
-- statement:
--   Let \(d>0\), let \(F_j\) be any real basis of traceless Hermitian operators on \(\mathbb C^d\), and set \(G_{jk}=\operatorname{Tr}(F_kF_j)\). Let \(H\) be Hermitian and \(K\) Hermitian, with no positivity assumption, and form the GKLS coordinate action \(\mathcal L\) using the minus-\(i\) Hamiltonian term and half anticommutator. Its trace on the entire complex operator space is
--   \[
--   \operatorname{Tr}\mathcal L=-d\,\operatorname{Tr}(KG).
--   \]
--   If \(G=I\) this is \(-d\operatorname{Tr}K\); if \(G=2I\) it is \(-2d\operatorname{Tr}K\). This trace is distinct from the always vanishing output trace \(\operatorname{Tr}(\mathcal L(\rho))\).
-- source:
--   The Geometry of Dissipative Complexity: A Levi-Type Decomposition Theorem for Markovian Quantum Dynamics via Lie Wedges and Invariant Cones, arXiv:2608.27330v1, PDF p. 12, Lemma 2.16: dissipation functional and normalizations

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P12

noncomputable section

open scoped Matrix ComplexOrder Matrix.Norms.Frobenius

open Set

namespace QAlgorithms.Papers.Independent.Dependency50.P12

attribute [local instance 100] LieRing.ofAssociativeRing

attribute [local instance] Classical.propDecidable Classical.decEq

open Coordinates

open QAlgorithms.Papers.Independent.Information100

/-- arXiv:2608.27330v1, PDF p.12, Lemma 2.16.
K is Hermitian and may be indefinite; the superoperator trace is on all B(H). -/
theorem dissipationFunctional {d : ℕ} (hd : 0 < d)
    (F : Fin (d^2-1) → P59.Operator d) (hF : P59.IsTracelessHermitianBasis F)
    (H : P59.Operator d) (hH : H.IsHermitian)
    (K : Matrix (Fin (d^2-1)) (Fin (d^2-1)) ℂ) (hK : K.IsHermitian) :
    P59.superoperatorTrace (P59.kossakowskiAction F H K) =
      -(d : ℂ) * (K * P59.gramMatrix F).trace ∧
    (P59.gramMatrix F = 1 →
      P59.superoperatorTrace (P59.kossakowskiAction F H K) = -(d : ℂ) * K.trace) ∧
    (P59.gramMatrix F = 2 • (1 : Matrix (Fin (d^2-1)) (Fin (d^2-1)) ℂ) →
      P59.superoperatorTrace (P59.kossakowskiAction F H K) =
        -2 * (d : ℂ) * K.trace) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P12

end
