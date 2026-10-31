-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P41_resolventInversion
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P41.resolventInversion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:33:01.345302+00:00
-- url     : https://prove2.me/theorems/8a14bc33-cff7-473e-ba45-e538bee7a20c
-- title:
--   Rank-one resolvent inversion
-- statement:
--   Let $d\ge1$, $P\in\operatorname{End}(\mathbb C^d)$, $Q=v\varphi$ with $\delta=\varphi(v)\ne0$, and $R=Q-P$. Assume the §18 simple-spectrum, nonresonance and general-position hypotheses for both $P$ and $R$, using eigenbases normalized by $\varphi=1$. Define $\chi_A(t)=1+\varphi((tI-A)^{-1}v)$ where the resolvent exists. For every $t\in\mathbb C$ for which $tI-R$ and $-tI-P$ are invertible,
--
--   $$\chi_R(t)=\chi_P(-t)^{-1}.$$
--
--   This is the common-resolvent-domain form of the source rational identity. The hypotheses avoid assigning total-inverse values at poles; the two determinant conditions also imply that the scalar being inverted is nonzero.
-- source:
--   Operator Algebras and Conformal Field Theory III. Fusion of positive energy representations of LSU(N) using bounded operators, arXiv:math/9806031v1, PDF p. 28, §22: Inversion lemma

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P41

noncomputable section

open scoped BigOperators

open MeasureTheory Set

namespace QAlgorithms.Papers.Independent.Intakenext100.P41

/-- §22 inversion lemma, PDF p.28. Pointwise form on the common resolvent
set; the excluded poles are essential because Lean's matrix inverse is total. -/
theorem resolventInversion {d : ℕ} (A : BasicODEData d) (t : ℂ)
    (hP : ((-t) • (1 : Matrix (Fin d) (Fin d) ℂ) - A.P).det ≠ 0)
    (hR : (t • (1 : Matrix (Fin d) (Fin d) ℂ) -
      (linearRankOneMatrix A.v A.phi - A.P)).det ≠ 0) :
    resolventScalar (linearRankOneMatrix A.v A.phi - A.P) A.v A.phi t =
      (resolventScalar A.P A.v A.phi (-t))⁻¹ := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P41

end
