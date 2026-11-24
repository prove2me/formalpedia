-- Prove2me | Theorems.Thm_RobustPMI_Hierarchy_Supplement_theorem_4_20
-- name    : RobustPMI.Hierarchy.Supplement.theorem_4_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T01:45:49.47491+00:00
-- url     : https://prove2.me/theorems/4df19eb5-7d36-4c13-98d7-c898054b2f88
-- title:
--   Theorem 4.20, p. 28 — smallest eigenvalue of a polynomial matrix: λ_k^primal ↗ λ⋆ and λ_k^dual ↗ λ⋆
-- statement:
--   Let $F\in\mathbb S[x]^m$ and $\lambda^\star=\inf_{x\in\mathcal X}\lambda_{\min}(F(x))$ (4.16). For $k\ge\max\{\lceil\deg F/2\rceil,\lceil\deg G/2\rceil\}$ let
--   $$\lambda_k^{\mathrm{primal}}=\inf_{S\in\mathcal M^m_k(G)}\{\mathscr L_S(F):\mathscr L_S(I_m)=1\},\qquad\lambda_k^{\mathrm{dual}}=\sup\{\lambda\in\mathbb R:F(x)-\lambda I_m\in\mathcal Q^m_k(G)\}$$
--   be the relaxations (4.18)–(4.19). Under Assumption 2,
--   $$\lambda_k^{\mathrm{primal}}\nearrow\lambda^\star\quad\text{and}\quad\lambda_k^{\mathrm{dual}}\nearrow\lambda^\star\qquad(k\to\infty).$$
--
--   **Formalization Note** Values are extended reals ($\lambda^\star=+\infty$ if $\mathcal X=\emptyset$); $\lambda_{\min}(A)$ is the minimum of $v^\top Av$ over unit vectors.
--
--   Differences from the source:
--   - encoding: λ_min(F(x)), the smallest eigenvalue; '↗'; values in ℝ ∪ {±∞} → min of the Rayleigh quotient over unit vectors; MonotoneOn on k ≥ max{⌈deg F/2⌉, ⌈deg G/2⌉} and Tendsto in EReal; reason: for a symmetric matrix the Rayleigh minimum is the smallest eigenvalue; Lean convention for the limits
-- source:
--   Guo, Wang, A moment-SOS hierarchy for robust polynomial matrix inequality optimization with SOS-convexity, arXiv:2304.12628v5, p. 28, Theorem 4.20

import Mathlib
import Definitions.Def_RobustPMI_Hierarchy_Model
import Definitions.Def_RobustPMI_Hierarchy_Supplement_Model

namespace RobustPMI.Hierarchy.Supplement

open MvPolynomial Matrix Filter Topology

/-- Theorem 4.20 (p. 28): under Assumption 2, `λ_k^primal ↗ λ⋆` and `λ_k^dual ↗ λ⋆` as
`k → ∞` (non-decreasing for `k ≥ max{⌈deg F/2⌉, ⌈deg G/2⌉}`). -/
theorem theorem_4_20 {n m q : ℕ} (F : Matrix (Fin m) (Fin m) (MvPolynomial (Fin n) ℝ))
    (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ))
    (hF : F.IsSymm) (hG : G.IsSymm) (h2 : Assumption2 G) :
    MonotoneOn (lamprimal F G) (Set.Ici (max ((degMat F + 1) / 2) ((degMat G + 1) / 2))) ∧
    MonotoneOn (lamdual F G) (Set.Ici (max ((degMat F + 1) / 2) ((degMat G + 1) / 2))) ∧
    Tendsto (lamprimal F G) atTop (𝓝 (lamstar F G)) ∧
    Tendsto (lamdual F G) atTop (𝓝 (lamstar F G)) := by sorry

end RobustPMI.Hierarchy.Supplement
