-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P09_su_choi
-- name    : QAlgorithms.Papers.Independent.Extend50.P09.su_choi
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:28:34.977953+00:00
-- url     : https://prove2.me/theorems/113eed2a-f701-434f-ba99-11493ff6a129
-- title:
--   Theorem 5: SU(d) Choi error
-- statement:
--   Fix an integer $d\ge2$. For $n\ge2$ let $\lambda$ partition $n-1$ with at most $d$ rows, and let $l_\lambda,r_\lambda$ be the actual Schur and Specht module dimensions. Append the physical isotypic embedding of $I_{L_\lambda}/l_\lambda\otimes|\psi_\lambda\rangle\langle\psi_\lambda|$, where $\psi_\lambda$ is a fixed unit Specht vector, to one logical $d$-level system. Conjugate by Haar measure on the determinant-one commutant of the collective $SU(d)$ action and erase one fixed known site. Errors mean optimal CPTP recovery measured in root-fidelity purified distance, with normalized Choi input and a decoder chosen before the worst reference-entangled input.
--
--   For fixed $\eta>0$, there are $C,c>0$ and $n_0$, independent of the allowed partitions, Specht vectors and erased positions, such that whenever $n\ge n_0$ and $n-\lambda_1\ge\eta n$, setting $B_n=\sqrt{d^2-1}/(2n)+C/n^2$ gives
--   $$\mathbb E \epsilon_{\rm Choi}\le B_n,\qquad\Pr[\epsilon_{\rm Choi}>B_n]\le e^{-cn}.$$
--
--   This preserves the printed theorem about optimal CPTP recovery. The printed complementary-channel proof drops the purification of a generally mixed ancilla; that proof gap is explicitly unresolved and is not turned into a hypothesis.
-- source:
--   Near-optimal covariant quantum error-correcting codes from random unitaries with symmetries, arXiv:2112.01498v2, PDF p. 11, Theorem 5: SU(d) Choi error

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P09

noncomputable section

open scoped Matrix Matrix.Norms.Elementwise ComplexConjugate ENNReal ComplexOrder

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Extend50.P09

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact generic definitions from the pinned accepted library.

open QAlgorithms.Papers.Independent.Information100.P22 (Op mixed bell)

open QAlgorithms.Papers.Independent.Information100.P67 (conditionalMinEntropy)

open QAlgorithms.Papers.Independent.Advance50.P02 (negLog)

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P09.covariantMatrixMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P09.covariantMatrixBorel

/-- Theorem 5, PDF pp.11–12, (82)–(83). This is the printed optimal CPTP
RECOVERY claim. Eq.(84)'s erased-qudit comparator omits an ancilla-purifying
register; that proof gap is disclosed in MODERATION_NOTES, not assumed away. -/
theorem su_choi (d : ℕ) (hd : 2 ≤ d) (laws : PhysicalUnitaryLaws d)
    (h : ∀ n, IsCommutantHaarLaw (SUGroup d n) (laws n)) :
    SUPerformance false d laws := by sorry

end QAlgorithms.Papers.Independent.Extend50.P09

end
