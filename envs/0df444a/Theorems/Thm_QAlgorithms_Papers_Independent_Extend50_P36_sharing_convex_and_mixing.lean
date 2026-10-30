-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P36_sharing_convex_and_mixing
-- name    : QAlgorithms.Papers.Independent.Extend50.P36.sharing_convex_and_mixing
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T14:02:28.755071+00:00
-- url     : https://prove2.me/theorems/60c737ca-0e38-4433-9e67-b5d6d63e1d38
-- title:
--   Sec. II B, unnumbered: convexity of sharing and mixing with separable states
-- statement:
--   For positive integers $m,n$, a state is $m$-$n$ sharable when a density operator on $H_L^{\otimes m}\otimes H_R^{\otimes n}$ has that same state as every left-right pair marginal. Arbitrary sharing means such an extension exists for every positive finite $m,n$.
--
--   Fix nonzero finite-dimensional local spaces and positive $m,n$. The set of $m$-$n$ sharable bipartite states is convex. The completely mixed state $\tau=I/(d_Ld_R)$ is arbitrarily sharable, and
--   $$\rho\text{ is }m\text{-}n\text{ sharable},\quad 0\le t\le1\quad\Longrightarrow\quad t\rho+(1-t)\tau\text{ is }m\text{-}n\text{ sharable}.$$
--   This records the convexity and mixed-state consequence stated in Sec.II B.
-- source:
--   Compatible quantum correlations: on extension problems for Werner and isotropic states, arXiv:1305.1342v3, PDF p. 5, Sec. II B, unnumbered: convexity of sharing and mixing with separable states

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P36

noncomputable section

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P36

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted matrix alias; tensor reductions below compose frozen superoperators.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

/-- Sec.II B, PDF p.5: sharing is convex; mixing with the fully mixed state preserves it. -/
theorem sharing_convex_and_mixing {I J : Type*} [Fintype I] [Fintype J]
    [Nonempty I] [Nonempty J] (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    Convex ℝ {rho : Op (I × J) | Sharable m n rho} ∧
    ArbitrarilySharable (fullyMixed (I × J)) ∧
    (∀ rho : Op (I × J), Sharable m n rho → ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      Sharable m n (convexStateMixture t rho (fullyMixed (I × J)))) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P36

end
