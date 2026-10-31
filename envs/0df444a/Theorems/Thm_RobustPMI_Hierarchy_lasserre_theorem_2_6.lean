-- Prove2me | Theorems.Thm_RobustPMI_Hierarchy_lasserre_theorem_2_6
-- name    : RobustPMI.Hierarchy.lasserre_theorem_2_6
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-31T00:15:42.496442+00:00
-- url     : https://prove2.me/theorems/f60a769e-27f6-4c5c-9087-8539fe879181
-- title:
--   Lasserre's extended Jensen inequality (Thm 2.6): $\mathscr H_s(h)\ge h(s_e)$ for SOS-convex $h$
-- statement:
--   Let $h\in\mathbb R[y]$, $y\in\mathbb R^\ell$, be **SOS-convex**: its Hessian $\nabla^2h$ is an SOS matrix. Let $s=(s_\alpha)_\alpha$ be a real sequence with $s_0=1$ whose moment matrix of order $d=\lceil\deg h/2\rceil$ is PSD, $M_d(s)\succeq0$. Let $\mathscr H_s(p)=\sum_\alpha p_\alpha s_\alpha$ be the associated linear functional and $s_e=(s_{e_1},\dots,s_{e_\ell})$. Then
--   $$\mathscr H_s(h)\ \ge\ h(s_e).$$
--
--   This is Lasserre's extension of Jensen's inequality. It applies to linear functionals that are only nonnegative on squares of degree $\le d$, not necessarily integration against a probability measure. Guo–Wang use it as [33, Theorem 2.6] in the proofs of Proposition 4.7 (p. 20, matrix version $\mathscr H_s(Q)\succeq Q(s_e)$ for PSD-SOS-convex $Q$) and of Corollary 4.8.
--
--   The proof in the source uses the Helton–Nie representation
--   $$h(y)-h(z)-\nabla h(z)^\top(y-z)=(y-z)^\top F(y)(y-z),\qquad F(y)=\int_0^1\!\!\int_0^t\nabla^2h(z+r(y-z))\,dr\,dt .$$
--   Here $F$ is an SOS matrix, so the left-hand side is an SOS polynomial and has nonnegative $\mathscr H_s$-value. One then takes $z=s_e$.
-- source:
--   J. B. Lasserre, Convexity in semialgebraic geometry and polynomial optimization, SIAM J. Optim. 19 (2009) 1995-2014 (arXiv:0806.3784), Theorem 2.6 (p. 6); cited as [33, Theorem 2.6] in Guo-Wang, arXiv:2304.12628v5, proofs of Proposition 4.7 and Corollary 4.8, p. 20

import Mathlib
import Definitions.Def_RobustPMI_Hierarchy_Model

namespace RobustPMI.Hierarchy

open MvPolynomial

/-- Lasserre (2009), Theorem 2.6 (extended Jensen inequality), as cited in Guo–Wang ([33, Theorem 2.6]):
if `h` is SOS-convex and `s` satisfies `s₀ = 1` and `M_{⌈deg h/2⌉}(s) ⪰ 0`, then `𝓗_s(h) ≥ h(s_e)`. -/
theorem lasserre_theorem_2_6 {ℓ : ℕ} (h : MvPolynomial (Fin ℓ) ℝ) (hh : IsSOSConvex h)
    (v : (Fin ℓ →₀ ℕ) → ℝ) (hv0 : v 0 = 1)
    (hM : (momentMat ((h.totalDegree + 1) / 2) (scalarSeq v)).PosSemidef) :
    eval (sE v) h ≤ Hs v h := by sorry

end RobustPMI.Hierarchy
