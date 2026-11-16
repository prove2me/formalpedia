-- Prove2me | Theorems.Thm_PrivateContinualCounting_Kraft_Supplement_hypertree_variance
-- name    : PrivateContinualCounting.Kraft.Supplement.hypertree_variance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:35:34.029206+00:00
-- url     : https://prove2.me/theorems/8cef2bb7-c2b2-4973-b3cf-e8745e77d4b8
-- title:
--   Lemma 5.3 — exact A/B/C variance at every local position
-- statement:
--   Fix $a>0$, $0<\xi<1$, and use the Section 5 square-root hypertree. For every positive time $t$ let $K=\lfloor\log_2t\rfloor$, $J=\lfloor\log_2(K+1)\rfloor$, $\tau=t-2^K+1$, $\kappa=K-(2^J-1)$, and let $q_J,y_J,z_J$ be the prescribed budgets. Its actual unit-noise variance is
--   $$\operatorname{Var}(N_t)=\sum_{j<J}\frac1{z_j}+\frac{S(\kappa)S(2^J)}{y_J}+\frac{S(\tau)S(2^K)}{1-q_J}.$$
--   Every published Gaussian counter whose factors and noise agree with these formulas has normalized variance $v_t=\operatorname{Var}(N_t)$ as well. The equality holds at every local position; $S(0)=0$ makes the middle term vanish at a super-epoch start. This is an exact law-of-the-construction equality, not a definition of the counter or an upper bound for its BLT variant.
--
--   Differences from the source:
--   - encoding: positive source time and stream indices → natural times with source input i+1 at coordinate i and zero-time noise zero; reason: the published base conventions are reused and every positive time and interval is retained
--   - encoding: the normalized variance of the constructed counter → the actual variance of the explicit seed sum, together with equality to every Gaussian-counter realization of it; reason: this states both meanings of the source variance and does not assume the identity
-- source:
--   Kisung Park, STOC 2027 submission #86 (October 2026), p. 12, PDF p. 14, Lemma 5.3

import Definitions.Def_PrivateContinualCounting_Kraft_Supplement_Hypertree

open MeasureTheory ProbabilityTheory Filter

set_option autoImplicit false

namespace PrivateContinualCounting.Kraft.Supplement

/-- Lemma 5.3: actual noise variance and normalized factor variance agree with
all three exact contributions, including zero B contribution when κ=0. -/
theorem hypertree_variance (a ξ : ℝ) (ha : 0 < a) (hξ0 : 0 < ξ) (hξ1 : ξ < 1) :
    ∀ t : ℕ, 1 ≤ t →
      let K := epoch t
      let J := superEpoch K
      let τ := localTime t
      let κ := localEpoch K
      treeVariance squareRootFamily a ξ t =
        (∑ j ∈ Finset.range J, 1 / zBudget a ξ j) +
        squareEnergy κ * squareEnergy (2^J) / yBudget a ξ J +
        squareEnergy τ * squareEnergy (2^K) / (1-qBudget a J) ∧
      ∀ M : GaussianCounter TreeIndex, IsTree M squareRootFamily a ξ →
        M.variance t = treeVariance squareRootFamily a ξ t := by sorry

end PrivateContinualCounting.Kraft.Supplement
