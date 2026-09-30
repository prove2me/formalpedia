-- Prove2me | Theorems.Thm_UnderstandingML_assignment_lp_integral
-- name    : UnderstandingML.assignment_lp_integral
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T04:54:35.236731+00:00
-- url     : https://prove2.me/theorems/37c93d5b-e77c-4916-8416-57221600ef3a
-- title:
--   Lemma 17.4: the assignment LP over doubly stochastic matrices has an optimal solution that is a permutation matrix
-- statement:
--   **Lemma 17.4.** There exists an optimal solution of Equation (17.10), $\operatorname{argmin}_B \langle A, B\rangle$ over doubly stochastic $B$, that is also an optimal solution of the assignment problem (17.9), i.e. a permutation matrix.
--
--   Formally: for every cost matrix $A$ there is a permutation $\sigma$ with $\langle A, P_\sigma\rangle \le \langle A, B\rangle$ for every doubly stochastic $B$.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §17.4.1 p. 243, Lemma 17.4 with its proof

import Definitions.Def_UnderstandingML_Multiclass

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- **Lemma 17.4** (p. 243). There exists an optimal solution of the linear program (17.10),
`min ⟨A, B⟩` over doubly stochastic `B`, that is also an optimal solution of the assignment
problem (17.9): a permutation matrix `C` with `⟨A, C⟩ ≤ ⟨A, B⟩` for every doubly stochastic `B`. -/
theorem assignment_lp_integral {r : ℕ} (A : Matrix (Fin r) (Fin r) ℝ) :
    ∃ σ : Equiv.Perm (Fin r), ∀ B ∈ doublyStochastic ℝ (Fin r),
      matrixInner A (σ.permMatrix ℝ) ≤ matrixInner A B := by sorry

end UnderstandingML
