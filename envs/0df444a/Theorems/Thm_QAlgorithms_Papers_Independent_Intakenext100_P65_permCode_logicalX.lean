-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P65_permCode_logicalX
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P65.permCode_logicalX
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:39:47.660994+00:00
-- url     : https://prove2.me/theorems/be072516-e5d3-414b-80cc-a7d2736e66df
-- title:
--   Collective qudit logical operator and coefficient transport
-- statement:
--   Let $d\ge2$, $M\ge1$ and $S\ge0$ be integers. Use the explicit shift $X=\sum_{
--   u=0}^{d-1}|
--   u\rangle\langle
--   u+1\pmod d|$, so that it shifts a basis label backwards. Let $X_{\rm col}=M^{-1}\sum_kX_k$ and let $P$ project to the extended-binomial excitation span of dimension $(d-1)M+1$. For the normalized Fourier repetition codewords and their excitation coefficients $v_\mu$,
--
--   $$X_{\rm col}|\mu_{\rm perm'}\rangle=e^{2\pi i\mu/d}|\mu_{\rm perm'}\rangle,\qquad (PX_{\rm col}P)v_\mu=e^{2\pi i\mu/d}v_\mu.$$
--
--   Transporting the latter action through $|m\rangle\mapsto|(S+1)m\rangle$ or $|m\rangle\mapsto|(S+1)((d-1)M-m),(S+1)m\rangle$ gives the same eigenphase on the one- and two-mode coefficient codes. The printed assertion about the Mth power being a check is not included.
-- source:
--   Performance and structure of single-mode bosonic codes, arXiv:1708.05010v3, PDF p. 28, Appendix C1 (C7)–(C11): collective logical operator and transport

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P65

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P65

open MeasureTheory Filter

open QAlgorithms.Papers.Independent.Frontier18.P14 (displacementEntry)

open QAlgorithms.Papers.Independent.Dependency50.P40 (outputFirstChoi)

open scoped ComplexConjugate Matrix Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF p.28 (C7)--(C11): positive Fourier eigenphase and its compression and
one-mode and two-mode transport. The erroneous Mth-power check is separately deferred.
Printed prose reverses C7 and omits one excitation dimension; use the displayed
C7 matrix with C8/C11 and all endpoints of C3/C4, hence dimension (d-1)M+1. -/
theorem permCode_logicalX (d M S : ℕ) (hd : 2 ≤ d) (hM : 0 < M) :
    (∀ mu : Fin d, (_root_.QAlgorithms.Papers.Independent.Intakenext100.P65.collectiveShift d M (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 1) hd)).mulVec (_root_.QAlgorithms.Papers.Independent.Intakenext100.P65.permCode d M mu) =
      _root_.QAlgorithms.Papers.Independent.Intakenext100.P65.quditFourierFactor d mu.val 1 • _root_.QAlgorithms.Papers.Independent.Intakenext100.P65.permCode d M mu) ∧
    (∀ mu : Fin d, (_root_.QAlgorithms.Papers.Independent.Intakenext100.P65.compressedShift d M (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 1) hd)).mulVec (_root_.QAlgorithms.Papers.Independent.Intakenext100.P65.extendedCoefficients d M mu) =
      _root_.QAlgorithms.Papers.Independent.Intakenext100.P65.quditFourierFactor d mu.val 1 • _root_.QAlgorithms.Papers.Independent.Intakenext100.P65.extendedCoefficients d M mu) ∧
    (∀ mu : Fin d,
      _root_.QAlgorithms.Papers.Independent.Intakenext100.P65.embedOne ((d - 1) * M) S ((_root_.QAlgorithms.Papers.Independent.Intakenext100.P65.compressedShift d M (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 1) hd)).mulVec (_root_.QAlgorithms.Papers.Independent.Intakenext100.P65.extendedCoefficients d M mu)) =
        _root_.QAlgorithms.Papers.Independent.Intakenext100.P65.quditFourierFactor d mu.val 1 • _root_.QAlgorithms.Papers.Independent.Intakenext100.P65.embedOne ((d - 1) * M) S (_root_.QAlgorithms.Papers.Independent.Intakenext100.P65.extendedCoefficients d M mu) ∧
      _root_.QAlgorithms.Papers.Independent.Intakenext100.P65.embedTwo ((d - 1) * M) S ((_root_.QAlgorithms.Papers.Independent.Intakenext100.P65.compressedShift d M (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 1) hd)).mulVec (_root_.QAlgorithms.Papers.Independent.Intakenext100.P65.extendedCoefficients d M mu)) =
        _root_.QAlgorithms.Papers.Independent.Intakenext100.P65.quditFourierFactor d mu.val 1 • _root_.QAlgorithms.Papers.Independent.Intakenext100.P65.embedTwo ((d - 1) * M) S (_root_.QAlgorithms.Papers.Independent.Intakenext100.P65.extendedCoefficients d M mu)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P65

end
