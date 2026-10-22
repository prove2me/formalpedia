-- Prove2me | Theorems.Thm_RandomGateDesign_MasterBound_fact_9
-- name    : RandomGateDesign.MasterBound.fact_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:27:49.638702+00:00
-- url     : https://prove2.me/theorems/9fcf5ab6-3e73-4b82-8f6e-7a6e2f44f2fe
-- title:
--   Fact 9 — irreducible decomposition indexed by dominant weights
-- statement:
--   For every $d,t\ge0$, the mixed tensor representation $U\mapsto U^{\otimes t}\otimes\overline U^{\otimes t}$ has a complete unitary decomposition into a trivial part and pairwise inequivalent nontrivial irreducible parts. The latter are indexed exactly by the nonzero dominant weights $\lambda\in\Lambda_t$ of zero total weight and positive-weight sum at most $t$: the block indexed by $\lambda$ is $\pi_\lambda$, the irreducible representation with highest weight $\lambda$ (with respect to the diagonal torus and the simple roots $L_i-L_{i+1}$). Their dimensions obey the Weyl formula:
--
--   $$\dim\pi_\lambda=d_\lambda=\prod_{1\le i<j\le d}\frac{\lambda_i-\lambda_j+j-i}{j-i}.$$
--
--   This connects the abstract block bounds to the explicit dimension sum in Theorem 1.
--
--   **Formalization Note** Highest weights are expressed through torus weights: the block indexed by $\lambda$ has $\lambda$ as a weight of the diagonal unitaries, and every other weight $\mu$ of that block satisfies $\mu\preceq\lambda$ in the dominance order. Indices are 0-based (`Fin d`). The decomposition structure includes isometries, orthogonality, completeness, intertwiners and pairwise inequivalence; the trailing equivalence with $(U\otimes\bar U)^{\otimes t}$ in (22) is a reordering of tensor factors and is not restated.
-- source:
--   Dulian & Sawicki, Matrix concentration inequalities and efficiency of random universal sets of quantum gates, arXiv:2202.05371v3, p. 12, Fact 9 and eqs. (22)–(23); p. 10, eq. (20)

import Definitions.Def_RandomGateDesign_MasterBound_Reps

noncomputable section

namespace RandomGateDesign.MasterBound

theorem fact_9 (d t : ℕ) :
    ∃ (r : ℕ) (D : MomentDecomposition d t r),
      ∃ e : Fin r ≃ {l : Fin d → ℤ // l ∈ Lambda d t},
        ∀ i : Fin r, HasHighestWeight (D.rep i) (e i).1 ∧
          (D.dim i : ℝ) = weylDim (e i).1 := by sorry

end RandomGateDesign.MasterBound
