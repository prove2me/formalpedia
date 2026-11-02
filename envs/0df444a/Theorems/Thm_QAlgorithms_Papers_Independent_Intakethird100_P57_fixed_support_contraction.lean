-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P57_fixed_support_contraction
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P57.fixed_support_contraction
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:12:20.624482+00:00
-- url     : https://prove2.me/theorems/5f5990ca-d9e6-4554-a172-f93a4b89a182
-- title:
--   Efficient computation: O(ND^5) per fixed-support marginal entry
-- statement:
--   Fix a support bound $s\ge0$. There are a constant $C_s>0$ and scalar programs, chosen before all numerical tensor, graph, rotation and operator data, with the following property. For all $N,D\ge1$, every subset $S$ with $|S|\le s$, all admissible RAGE data with nonzero raw MPS, and every operator $O$ on $S$, the program computes all intermediate transfer products, the cross-edge kernel, the positive normalization, every normalized marginal entry, and $\operatorname{tr}(O\rho_S)$ exactly, using
--
--   $$\mathrm{work}\le C_sND^5.$$
--
--   Work counts executed scalar reads, arithmetic, conjugation, and the specified phase evaluations; division by zero fails explicitly. No product-evaluator oracle is allowed. The full output still contains $4^{|S|}$ marginal entries. This is ideal scalar complexity, with the sum-of-Kronecker structure retained; it makes no finite-precision or polynomial-in-$s$ claim. It supplies local and arbitrarily separated two-site expectations.
-- source:
--   Renormalization algorithm with graph enhancement, arXiv:0802.1211v1, PDF p. 2, Efficient computation: O(ND^5) per fixed-support marginal entry

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P57

noncomputable section

open scoped ComplexConjugate Matrix

namespace QAlgorithms.Papers.Independent.Intakethird100.P57

attribute [local instance] Classical.propDecidable

/-- PDF pp.2–3: exact fixed-support computation in O(ND⁵) ideal scalar work, uniformly
in all tensor/graph/rotation/observable data. Entire marginals retain the 4^|S| output size.
No dense D²-by-D² multiplication is treated as an atomic instruction: the implementation
must retain the sum-of-Kronecker structure to meet this bound. Constants and programs precede
all numerical data. A supplied list of local terms is evaluated term by term and summed. -/
theorem fixed_support_contraction :
    ∀ s : ℕ, ∃ C : ℕ, 0 < C ∧
      ∃ programs : (N D : ℕ) → (S : Finset (Fin N)) → MarginalProgram N D S,
      ∀ (N D : ℕ) (S : Finset (Fin N)), 1 ≤ N → 1 ≤ D → S.card ≤ s →
        let p := programs N D S
        p.scalar.calls = 0 ∧ p.scalar.work 0 ≤ C * N * D ^ 5 ∧
        (∀ (A : Tensors N D) (G : PhaseGraph N) (V : Fin N → Matrix.unitaryGroup Bool ℂ)
          (O : Matrix (S → Bool) (S → Bool) ℂ), traceMPS A ≠ 0 → p.Correct A G V O) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P57

end
