-- Prove2me | Theorems.Thm_RobustPMI_Hierarchy_Supplement_lemma_5_1
-- name    : RobustPMI.Hierarchy.Supplement.lemma_5_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T01:47:00.867024+00:00
-- url     : https://prove2.me/theorems/61dffbec-0bdb-4a1c-a8a6-5dd97238b866
-- title:
--   Lemma 5.1, p. 29 — Jensen's inequality for PSD-convex polynomial matrices: 𝓗_s(Q) ⪰ Q(s_e)
-- statement:
--   Let $Q(y)\in\mathbb S[y]^m$ be PSD-convex in $y$ (Definition 2.3): $tQ(y^{(1)})+(1-t)Q(y^{(2)})\succeq Q(ty^{(1)}+(1-t)y^{(2)})$ for all $y^{(1)},y^{(2)}\in\mathbb R^\ell$, $t\in(0,1)$. If a sequence $s=(s_\alpha)_{\alpha\in\mathbb N^\ell}$ admits a representing probability measure $\mu$ ($s_\alpha=\int y^\alpha d\mu$ for all $\alpha$), then
--   $$\mathscr H_s(Q(y))\succeq Q(s_e),$$
--   where $\mathscr H_s$ is the Riesz functional applied entrywise and $s_e=(s_{e_1},\dots,s_{e_\ell})$.
--
--   This is the Jensen inequality used to show that the barycenter of a representing measure is feasible in the general convex setting (Theorems 5.2 and 5.4).
--
--   **Formalization Note** A representing probability measure is a Borel probability measure on $\mathbb R^\ell$ against which every monomial is integrable.
--
--   Differences from the source: none.
-- source:
--   Guo, Wang, A moment-SOS hierarchy for robust polynomial matrix inequality optimization with SOS-convexity, arXiv:2304.12628v5, p. 29, Lemma 5.1

import Mathlib
import Definitions.Def_RobustPMI_Hierarchy_Model
import Definitions.Def_RobustPMI_Hierarchy_Supplement_Model

namespace RobustPMI.Hierarchy.Supplement

open MvPolynomial Matrix Filter Topology

/-- Lemma 5.1 (p. 29, Jensen's inequality for PSD-convexity): if `Q(y) ∈ 𝕊[y]^m` is PSD-convex in
`y` and `s = (s_α)_{α ∈ ℕ^ℓ}` admits a representing probability measure, then
`𝓗_s(Q(y)) ⪰ Q(s_e)`. -/
theorem lemma_5_1 {ℓ m : ℕ} (Q : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ) ℝ))
    (hQ : Q.IsSymm) (hconv : IsPSDConvex Q) (sv : (Fin ℓ →₀ ℕ) → ℝ) (hs : HasRepProb sv) :
    (Q.map (Hs sv) - Q.map (eval (sE sv))).PosSemidef := by sorry

end RobustPMI.Hierarchy.Supplement
