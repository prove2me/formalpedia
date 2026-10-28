-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P26_appendixA_rate_elimination
-- name    : QAlgorithms.Papers.Independent.Support50.P26.appendixA_rate_elimination
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T21:06:38.256256+00:00
-- url     : https://prove2.me/theorems/31d01e07-2b6e-467c-baa3-0a79b1df81bd
-- title:
--   Appendix A: exact elimination of the auxiliary rates
-- statement:
--   For any channel, joint auxiliary law, and deterministic map defining a Marton state $\theta$, write $a=I(U_1;B_1)_\theta$, $b=I(U_2;B_2)_\theta$, and $c=I(U_1;U_2)_\theta$. For every nonnegative rate pair $(R_1,R_2)$, the existence of real auxiliary rates $t_1,t_2$ satisfying all seven constraints
--   $$
--   R_1+R_2+c\le t_1+t_2,\quad 2t_1+t_2\le a+2R_1+R_2+c,\quad t_1\le a,
--   $$
--   $$
--   2t_2+t_1\le b+2R_2+R_1+c,\quad t_2\le b,\quad R_1\le t_1,\quad R_2\le t_2
--   $$
--   is equivalent to
--   $$
--   R_1\le a,\qquad R_2\le b,\qquad R_1+R_2\le a+b-c.
--   $$
--   This identifies exactly the projection used in deriving the Marton region and preserves both lower bounds on the eliminated rates.
-- source:
--   Classical codes for quantum broadcast channels, arXiv:1111.3645v4, PDF p. 14, Appendix A: projection of the seven auxiliary-rate inequalities is precisely the Marton region

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P26

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Support50.P26

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact primitives from pinned accepted modules, under the independent-paper override.
-- No coding theorem or other paper's channel model is reused.

open QAlgorithms.Papers.Independent.Information100.P22 (Op quantumMI)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Claimed50.P08 (cqBlocks)

open QAlgorithms.Papers.Independent.Dependency50.P47 (Law)

variable {X B1 B2 W U V A B : Type}

variable [Fintype X] [Fintype B1] [Fintype B2] [Fintype W] [Fintype U] [Fintype V]

variable [Fintype A] [Fintype B]

variable [DecidableEq X] [DecidableEq B1] [DecidableEq B2] [DecidableEq W]

variable [DecidableEq U] [DecidableEq V] [DecidableEq A] [DecidableEq B]

/-- Appendix A, PDF pp.14–16: exact projection of the seven constraints for every actual
Marton state and nonnegative target pair. Both auxiliary-rate lower bounds are retained. -/
theorem appendixA_rate_elimination (C : BroadcastChannel X B1 B2) (D : MartonData U V X)
    (r : ℝ × ℝ) (h1 : 0 ≤ r.1) (h2 : 0 ≤ r.2) :
    (∃ t1 t2 : ℝ, auxiliaryRateSystem
      (quantumMI (martonU1B1 C D)) (quantumMI (martonU2B2 C D)) (auxiliaryMI D) r t1 t2) ↔
    r ∈ MartonRegion C D := by sorry

end QAlgorithms.Papers.Independent.Support50.P26

end
