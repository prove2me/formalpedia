-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P28_operation_optimum
-- name    : QAlgorithms.Papers.Independent.Claimed50.P28.operation_optimum
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:13:50.431626+00:00
-- url     : https://prove2.me/theorems/256a390d-cb16-4903-b8ff-78f7e59a3da1
-- title:
--   Optimal full-operation tomography: global lower bound and attainment
-- statement:
--   Let $d\ge1$ be the common input and output dimension. The prior mean Choi matrix is $I_{\rm out}\otimes I_{\rm in}/d$, and the representation operator is the identity on Hilbert–Schmidt operator space. A physical tester has positive density $\Pi_x$ with integral $I_{\rm out}\otimes\sigma$, where $\sigma$ is a density matrix. A dual $\Delta_x$ reconstructs every operator in the complex span of all completely positive trace-nonincreasing operations. Assume all reconstruction integrals and the second moment are finite. Then every such tester and dual satisfy
--
--   $$\eta=\frac1d\int\operatorname{Tr}(\Pi_x)\|\Delta_x\|_{\rm HS}^2\,dx\ \ge\ d^6+d^4-d^2.$$
--
--   Equality is attained by the single-seed $SU(d)\times SU(d)$ orbit of $d|\Psi\rangle\!\rangle\langle\!\langle\Psi|$, where $\Psi=\sqrt{(1-\beta)I/d+\beta|\psi\rangle\langle\psi|}$, $\|\psi\|=1$, and $\beta=\sqrt{(d+1)/(d^2+1)}$. Its target frame is complete and has an attaining unbiased dual. The physical preparation is $|I\rangle\!\rangle/\sqrt d$ and the POVM density is $d\Pi$. This gives a global single-sample variance optimum; at $d=1$ it equals $1$.
-- source:
--   Optimal quantum tomography for states, measurements, and transformations, arXiv:0806.1172v1, PDF p. 3, (34), first line; (36)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P28

noncomputable section

open MeasureTheory

open scoped BigOperators ComplexConjugate ComplexOrder Matrix Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Claimed50.P28

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted aliases/pairing; unrelated short-name collisions are not reused.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

/-- PDF p.3, (34) first line, and p.4, (36): global full-operation minimum and attainment.
This is uniform over physical testers and unbiased duals, not just a scalar minimization of (33). -/
theorem operation_optimum {d : ℕ} (hd : 0 < d)
    (haar : Measure (SU d)) (hhaar : IsProbabilityHaar haar) :
    (∀ (X : Type) [MeasurableSpace X] (mu : Measure X) [SFinite mu]
      (P D : X → Op (ChoiBasis d)), TomographyAdmissible mu P D .operations →
      (d : ℝ)^6 + (d : ℝ)^4 - (d : ℝ)^2 ≤ eta .operations mu P D) ∧
    (∀ psi : EuclideanSpace ℂ (Fin d), QAlgorithms.IsState psi → Attains haar .operations psi) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P28

end
