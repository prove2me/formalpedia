-- Prove2me | Theorems.Thm_RobustPMI_Hierarchy_proposition_4_6
-- name    : RobustPMI.Hierarchy.proposition_4_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:18:07.201311+00:00
-- url     : https://prove2.me/theorems/3096ec2b-8962-4e02-9287-6b0d1608ad28
-- title:
--   Proposition 4.6, p. 19 — (f_k^primal) and (f_k^dual) are non-increasing upper bounds on f⋆
-- statement:
--   Let (RPMIO) have an optimal solution and let Assumptions 1 and 3 hold. For the moment-SOS hierarchy (4.4)–(4.5), the sequences
--   $$\big(f^{\mathrm{primal}}_k\big)_{k\ge\lceil k_x/2\rceil}\quad\text{and}\quad\big(f^{\mathrm{dual}}_k\big)_{k\ge\lceil k_x/2\rceil}$$
--   are monotonically non-increasing in the relaxation order $k$, and every term is an upper bound on the robust optimum:
--   $$f^\star\le f^{\mathrm{primal}}_k,\qquad f^\star\le f^{\mathrm{dual}}_k\qquad(k\ge\lceil k_x/2\rceil).$$
--
--   Unlike the usual Lasserre hierarchy, which approximates the optimum from below, this hierarchy restricts the robust constraint and approaches $f^\star$ from above. Assumption 2 is not needed here.
--
--   **Formalization Note** Both values are extended reals ($f^{\mathrm{dual}}_k=+\infty$ when (4.5) is infeasible), and $f^\star$ is coerced to the extended reals. The standing assumption of p. 2 (an optimizer exists) and the symmetry of $P$ and $G$ are hypotheses.
-- source:
--   Guo, Wang, A moment-SOS hierarchy for robust polynomial matrix inequality optimization with SOS-convexity, arXiv:2304.12628v5, p. 19, Proposition 4.6

import Mathlib
import Definitions.Def_RobustPMI_Hierarchy_Model

namespace RobustPMI.Hierarchy

/-- Proposition 4.6 (p. 19): under Assumptions 1 and 3 (and the standing assumption that (RPMIO) has
an optimizer), `(f_k^primal)_{k ≥ ⌈k_x/2⌉}` and `(f_k^dual)_{k ≥ ⌈k_x/2⌉}` are non-increasing and
bounded below by `f⋆`. -/
theorem proposition_4_6 {ℓ n m q s : ℕ} (f : MvPolynomial (Fin ℓ) ℝ)
    (θ : Fin s → MvPolynomial (Fin ℓ) ℝ)
    (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ))
    (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ))
    (hP : P.IsSymm) (hG : G.IsSymm)
    (h1 : Assumption1 f θ P G) (h3 : Assumption3 θ P G)
    (hmin : ∃ y, IsGlobalMin f θ P G y) :
    AntitoneOn (fprimal f θ P G) (Set.Ici ((kx P G + 1) / 2)) ∧
      AntitoneOn (fdual f θ P G) (Set.Ici ((kx P G + 1) / 2)) ∧
      ∀ k : ℕ, (kx P G + 1) / 2 ≤ k →
        (fstar f θ P G : EReal) ≤ fprimal f θ P G k ∧ (fstar f θ P G : EReal) ≤ fdual f θ P G k := by sorry

end RobustPMI.Hierarchy
