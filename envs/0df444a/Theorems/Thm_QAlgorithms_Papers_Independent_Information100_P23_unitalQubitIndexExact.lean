-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P23_unitalQubitIndexExact
-- name    : QAlgorithms.Papers.Independent.Information100.P23.unitalQubitIndexExact
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:14:11.22223+00:00
-- url     : https://prove2.me/theorems/62f61365-95c1-48d6-8c09-36177f8bb09a
-- title:
--   §6 unnumbered: exact index on unital qubit channels
-- statement:
--   Fix a normalized qubit Bloch basis, and let $\Phi$ be a unital CPTP qubit map, meaning $\Phi(I)=I$. Its computed affine data have $c=0$. With all crossing times minimized over positive integers and empty minima equal to infinity,
--
--   $$n_{\mathrm{EB}}(\Phi)=\nu_2(A,c)=\nu_{\mathrm{blind}}(A)=\min\{n\ge1:\|A^n\|_*\le1\}.$$
--
--   This makes the quadratic lower bound exact on every unital qubit channel, using the credited unital converse of Ruskai. No contraction, normality, or finite-index assumption is made; unitary channels are included.
-- source:
--   A sharp norm inequality for entanglement-breaking channels, arXiv:2609.27906v1, PDF p. 4, §6 unnumbered: exact index on unital qubit channels

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P23

noncomputable section

open scoped Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Information100.P23

/-- PDF p.4, §6: exact index of every unital CPTP qubit channel, using Ruskai's
converse. No contraction, diagonalization, or eventual-EB assumption is imposed. -/
theorem unitalQubitIndexExact (B : BlochBasis 2) (Phi : ChannelMap 2)
    (hPhi : IsCPTP Phi) (hunital : Phi 1 = 1) :
    blochC B Phi = 0 ∧
    entanglementBreakingIndex Phi = quadraticCrossingIndex (d := 2) (blochA B Phi) (blochC B Phi) ∧
    quadraticCrossingIndex (d := 2) (blochA B Phi) (blochC B Phi) = blindCrossingIndex (d := 2) (blochA B Phi) ∧
    entanglementBreakingIndex Phi =
      positiveIndex (fun n => nuclearNorm (blochA B Phi ^ n) ≤ 1) := by sorry

end QAlgorithms.Papers.Independent.Information100.P23

end
