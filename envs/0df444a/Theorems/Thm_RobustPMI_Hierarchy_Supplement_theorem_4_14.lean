-- Prove2me | Theorems.Thm_RobustPMI_Hierarchy_Supplement_theorem_4_14
-- name    : RobustPMI.Hierarchy.Supplement.theorem_4_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T01:44:24.027802+00:00
-- url     : https://prove2.me/theorems/3751bbe4-ce2a-49f4-bce9-11ca6de580f8
-- title:
--   Theorem 4.14, p. 23 — no duality gap between (4.4) and (4.5) under Assumption 4
-- statement:
--   Suppose Assumption 4 holds: (i) $\theta_1(y)=b^2-\sum_{i=1}^\ell y_i^2$ for some $b\ne0$, and (ii) $\mathcal X$ has nonempty interior. Then for each $k\ge\lceil k_x/2\rceil$,
--   $$f_k^{\mathrm{primal}}=f_k^{\mathrm{dual}},$$
--   where $f_k^{\mathrm{primal}}$ and $f_k^{\mathrm{dual}}$ are the optimal values of the primal SOS relaxation (4.4) and the dual moment relaxation (4.5).
--
--   Strong duality makes the condition $f_k^{\mathrm{primal}}=f_k^{\mathrm{dual}}$ of Theorem 4.11 automatic.
--
--   **Formalization Note** The values are extended reals, so the equality includes the infeasible and unbounded cases.
--
--   Differences from the source:
--   - encoding: extended values of the relaxations → EReal sSup/sInf, compared with the real f⋆ coerced to EReal; reason: Lean convention; low orders can be infeasible or unbounded
-- source:
--   Guo, Wang, A moment-SOS hierarchy for robust polynomial matrix inequality optimization with SOS-convexity, arXiv:2304.12628v5, p. 23, Theorem 4.14

import Mathlib
import Definitions.Def_RobustPMI_Hierarchy_Model
import Definitions.Def_RobustPMI_Hierarchy_Supplement_Model

namespace RobustPMI.Hierarchy.Supplement

open MvPolynomial Matrix Filter Topology

/-- Theorem 4.14 (p. 23): under Assumption 4, `f_k^primal = f_k^dual` for each `k ≥ ⌈k_x/2⌉`. -/
theorem theorem_4_14 {ℓ n m q s : ℕ} (f : MvPolynomial (Fin ℓ) ℝ)
    (θ : Fin s → MvPolynomial (Fin ℓ) ℝ)
    (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ))
    (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ))
    (hP : P.IsSymm) (hG : G.IsSymm) (h4i : Assumption4i θ) (h4ii : Assumption4ii G)
    (k : ℕ) (hk : (kx P G + 1) / 2 ≤ k) :
    fprimal f θ P G k = fdual f θ P G k := by sorry

end RobustPMI.Hierarchy.Supplement
