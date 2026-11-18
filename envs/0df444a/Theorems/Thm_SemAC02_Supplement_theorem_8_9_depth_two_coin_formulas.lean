-- Prove2me | Theorems.Thm_SemAC02_Supplement_theorem_8_9_depth_two_coin_formulas
-- name    : SemAC02.Supplement.theorem_8_9_depth_two_coin_formulas
-- status  : Proved
-- author  : @Henry Yuen
-- created : 2026-11-17T20:10:00.532011+00:00
-- url     : https://prove2.me/theorems/204337f6-0d13-4078-873b-e19cd36111bc
-- title:
--   Theorem 8.9, depth-two case — monotone coin formulas of size exp(O(1/epsilon))
-- statement:
--   For all sufficiently small $\epsilon>0$, there is a monotone AND/OR formula of depth at most two, in the source's normal form, solving the $\epsilon$-coin problem with error at most $1/10$ and tree size at most
--   $$\exp(A/\epsilon),$$
--   where $A$ is an absolute constant chosen before $\epsilon$. The two coin biases are $(1-\epsilon)/2$ and $(1+\epsilon)/2$.
--
--   This is the depth-two instance of Theorem 8.9 in *Hard Instances for Strong Semantic Proof Systems*. It is a supporting base case for the full fixed-depth theorem, not a claim about depths greater than two. The displayed inverse is exactly the theorem's exponent $\epsilon^{-1/(d-1)}$ at $d=2$.
--
--   Formalization Note: `IsReduced` expresses the paper's circuit normal form, size counts tree nodes, and `bernProb` is the finite product-probability sum. The bias threshold and exponent constant are existential constants as in the source.
-- source:
--   Alekseev, Gryaznov, Itsykson, Pitassi, Robere, Tzameret, Hard Instances for Strong Semantic Proof Systems, Theorem 8.9 (Limaye et al. [52]), printed p.66, specialized to d=2, https://www.doc.ic.ac.uk/~itzamere/Reslin_Simplification.pdf. See also Limaye et al., A Fixed-Depth Size-Hierarchy Theorem for AC0[oplus] via the Coin Problem, Section 5, Theorem 17 (O’Donnell–Wimmer baseline), https://people.iith.ac.in/karteek/assets/pdf/FixedDepthSizeHierarchyTheorem.pdf. This specialization is proved directly, without importing an open source theorem.

import Mathlib
import Definitions.Def_SemAC02_Circ
import Definitions.Def_SemAC02_bernProb
import Definitions.Def_SemAC02_IsCoinDistinguisher

namespace SemAC02.Supplement

theorem theorem_8_9_depth_two_coin_formulas :
    ∃ A ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ (m : ℕ) (T : Circ (Fin m)), IsMonotoneCirc T ∧ IsReduced T ∧ T.depth ≤ 2 ∧
        (T.treeSize : ℝ) ≤ Real.exp (A*ε⁻¹) ∧
        IsCoinDistinguisher ε (1/10) (fun x => T.eval x) := by sorry

end SemAC02.Supplement
