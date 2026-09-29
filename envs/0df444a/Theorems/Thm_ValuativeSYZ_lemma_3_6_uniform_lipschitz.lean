-- Prove2me | Theorems.Thm_ValuativeSYZ_lemma_3_6_uniform_lipschitz
-- name    : ValuativeSYZ.lemma_3_6_uniform_lipschitz
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T11:46:02.564798+00:00
-- url     : https://prove2.me/theorems/62f9637f-1c24-431e-a0c5-efce3e73a3f4
-- title:
--   Lemma 3.6 (Lipschitz part): functions in $P_c$ are uniformly Lipschitz
-- statement:
--   **Lemma 3.6, Lipschitz part.** If the cost function is uniformly Lipschitz in its first variable —
--   in the paper this is the uniform Lipschitz estimate $\sup_{p}|c(x,p) - c(x',p)| \le C|x - x'|$
--   inherited from Lemma 2.3 — then every function of the class $P_c$ is Lipschitz with the same
--   constant.
--
--   This is the equicontinuity that makes $P_c$ precompact in the uniform topology on the skeleton, and
--   that lets the limiting tropical theta functions be extracted as uniform limits.
-- source:
--   Yang Li, *Valuative independence and metric SYZ conjecture*, arXiv:2605.00516v1 (1 May 2026), https://arxiv.org/abs/2605.00516, pp. 15, Lemma 3.6 (Lipschitz assertion; uses estimate (9))

import Mathlib
import Definitions.Def_ValuativeSYZ_cost_transform
import Definitions.Def_ValuativeSYZ_degeneration

set_option autoImplicit false

open MeasureTheory

namespace ValuativeSYZ

/-- **Lemma 3.6 (Lipschitz part).** If the cost function is uniformly Lipschitz in its first
variable, then every function of the class `P_c` is Lipschitz with the same constant. -/
theorem lemma_3_6_uniform_lipschitz {X B : Type*} [PseudoMetricSpace X] [Nonempty B]
    (c : X → B → ℝ) (Kc : NNReal) (M : ℝ)
    (hc : ∀ x p, |c x p| ≤ M) (hlip : ∀ p, LipschitzWith Kc fun x => c x p)
    (φ : X → ℝ) (hφ : φ ∈ Pc c) : LipschitzWith Kc φ := by sorry

end ValuativeSYZ
