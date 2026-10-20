-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P67_optimizedMarginalComparison
-- name    : QAlgorithms.Papers.Independent.Information100.P67.optimizedMarginalComparison
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:03:24.556605+00:00
-- url     : https://prove2.me/theorems/3e1e8c15-9fc2-4e32-972f-e408866230ca
-- title:
--   Proposition D.1 (Optimized and actual-marginal fidelities)
-- statement:
--   For every valid unassisted finite-block code of any finite-dimensional channel, use squared fidelity and one common ideal environment state. Let $f$ denote its optimized joint fidelity, $f_{\rm marg}$ the joint fidelity with the actual environment marginal, and $\varepsilon=1-f$, $\varepsilon_{\rm marg}=1-f_{\rm marg}$. Then
--
--   $$f_{\rm marg}\le f,\qquad \varepsilon\le\varepsilon_{\rm marg}\le\min\{1,4\varepsilon\}.$$
--
--   The two uniform criteria have equal vanishing-error operational capacity. Every real finite-block upper bound on $f$ also bounds $f_{\rm marg}$. Degradability is not assumed, and equality of finite-error fidelities is not asserted.
-- source:
--   An exponential strong converse for private communication over degradable quantum channels, arXiv:2609.32515v1, PDF p. 47, Proposition D.1 (Optimized and actual-marginal fidelities)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Information100.P67

variable {A B E R S T X C Y G1 G2 : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype E] [DecidableEq E] [Fintype R] [DecidableEq R]

variable [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]

variable [Fintype X] [DecidableEq X] [Fintype C] [DecidableEq C]

variable [Fintype Y] [DecidableEq Y] [Fintype G1] [DecidableEq G1]

variable [Fintype G2] [DecidableEq G2]

/-- Proposition D.1, PDF p.47. No degradability assumption. Includes the
capacity consequence and arbitrary finite-block upper-bound transfer. -/
theorem optimizedMarginalComparison [Nonempty A] [Nonempty B] [Nonempty E]
    (U : Matrix (B × E) A ℂ) (hU : IsIsometry U) :
    (∀ n (code : PrivateCode A B n), code.Valid →
      marginalFidelity U code ≤ optimizedFidelity U code ∧
      uniformError U code ≤ marginalError U code ∧
      marginalError U code ≤ min 1 (4 * uniformError U code) ∧
      (∀ bound : ℝ, optimizedFidelity U code ≤ bound → marginalFidelity U code ≤ bound)) ∧
    privateCapacity .uniformOptimized U = privateCapacity .actualMarginal U := by sorry

end QAlgorithms.Papers.Independent.Information100.P67

end
