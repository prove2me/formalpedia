-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P45_dampingDiagonalOptimization
-- name    : QAlgorithms.Papers.Independent.Dependency50.P45.dampingDiagonalOptimization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T17:07:17.956982+00:00
-- url     : https://prove2.me/theorems/1c8fd335-5c1c-47af-9d49-851cf639c41e
-- title:
--   §III.B: one-parameter optimization for amplitude-damping C_E
-- statement:
--   For $0\le p\le1$, let $\mathcal D_p$ be the qubit amplitude-damping channel with Kraus operators $\operatorname{diag}(1,\sqrt{1-p})$ and $\sqrt p\,|0\rangle\langle1|$. For $0\le x\le1$, put $\rho_x=\operatorname{diag}(1-x,x)$ and let $h_2(t)=-t\log_2t-(1-t)\log_2(1-t)$ with the endpoint convention $0\log0=0$. The normalized-purification mutual information at $\rho_x$ equals $J_E(p,x)=h_2(x)+h_2((1-p)x)-h_2(px)$, and the operational capacity with unlimited prior EPR pairs and uniformly vanishing message error satisfies the attained optimization
--
--   $$C_E(\mathcal D_p)=\max_{0\le x\le1}J_E(p,x).$$
--
--   All rates are in bits. This makes the symmetry reduction to diagonal inputs explicit while preserving operational capacity as a separately defined object.
-- source:
--   Entanglement-assisted capacity of a quantum channel and the reverse Shannon theorem, arXiv:quant-ph/0106052v2, PDF p. 34, §III.B: one-parameter optimization for amplitude-damping C_E

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P45

noncomputable section

open scoped ComplexConjugate Matrix

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Dependency50.P45

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)

open QAlgorithms.Papers.Independent.Information100.P76 (dampingChannel)

/-- PDF p.34: operational capacity is attained by a diagonal input, with scalar formula. -/
theorem dampingDiagonalOptimization (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (∀ x ∈ Set.Icc (0 : ℝ) 1,
      inputMutualInfo (dampingChannel p 1) (dampingInput x) = dampingEAObjective p x) ∧
    ∃ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 ∧
      resourceCapacity standardEbit (dampingChannel p 1) = inputMutualInfo (dampingChannel p 1) (dampingInput x) ∧
      ∀ y ∈ Set.Icc (0 : ℝ) 1, dampingEAObjective p y ≤ dampingEAObjective p x := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P45

end
