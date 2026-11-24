-- Prove2me | Theorems.Thm_RobustPMI_Hierarchy_Supplement_theorem_4_3
-- name    : RobustPMI.Hierarchy.Supplement.theorem_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T01:42:50.154801+00:00
-- url     : https://prove2.me/theorems/d22393eb-0218-4d31-a7d7-1551b53eb677
-- title:
--   Theorem 4.3, p. 18 — the conic reformulation is exact: f̃ = f̂ = f⋆
-- statement:
--   Consider (RPMIO): minimize $f(y)$ over $y\in\mathcal Y$ subject to $P(y,x)\succeq0$ for all $x\in\mathcal X$, with optimal value $f^\star$. Let $\tilde f$ be the value of the conic program (4.2),
--   $$\tilde f=\sup\{\rho\in\mathbb R:\ f(y)-\rho-\mathscr L_\Phi(P(y,x))\in\mathcal P(\mathcal Y),\ \Phi\in\mathfrak M^m_+(\mathcal X)\},$$
--   where $\mathfrak M^m_+(\mathcal X)$ is the cone of PSD matrix-valued measures on $\mathcal X$ and $\mathcal P(\mathcal Y)$ the cone of polynomials nonnegative on $\mathcal Y$, and let $\hat f$ be the value of its dual (4.3),
--   $$\hat f=\inf\{\mathscr H_\mu(f):\ \mu\in\mathfrak m_+(\mathcal Y),\ \mathscr H_\mu(1)=1,\ \mathscr H_\mu(P(y,x))\in\mathcal P^m(\mathcal X)\},$$
--   with $\mathscr H_\mu(h)=\int h\,d\mu$. Under Assumptions 1 (SOS-convexity of $f,-\theta_j$, PSD-SOS-convexity of $-P(\cdot,x)$, compact $\mathcal X$) and 3 (Slater point), and the standing assumption that (RPMIO) has an optimal solution,
--   $$\tilde f=\hat f=f^\star.$$
--
--   The theorem shows that (RPMIO) is equivalent to a pair of linear conic programs over measures, which the moment-SOS hierarchy then approximates.
--
--   **Formalization Note** Values are extended reals. $\Phi$ ranges over all PSD matrix-valued measures (finite signed Borel entries, symmetric, PSD on every Borel set, vanishing outside $\mathcal X$), not only atomic ones; $\mu$ over all finite Borel measures on $\mathbb R^\ell$ with $\mu(\mathcal Y^c)=0$ that integrate every polynomial.
--
--   Differences from the source:
--   - reading: the theorem's own hypotheses (the paper assumes once, on p. 2, that the optimal set of (RPMIO) is nonempty) → hypothesis ∃ y, IsGlobalMin f θ P G y; reason: the p. 2 standing assumption governs every statement about f⋆; without it the real infimum f⋆ is a junk value
--   - reading: 𝓛_Φ and 𝓗_µ applied to all polynomials → every polynomial is integrable against |ϕ_ij| and against µ; reason: the paper defines 𝓗_µ as a linear functional on all of ℝ[y] (p. 18) and 𝓛_Φ on all of 𝕊[x]^m (Definition 2.8), which presupposes integrability; for Φ it is automatic here since 𝒳 is compact under Assumption 1
--   - encoding: f̃, f̂ in ℝ ∪ {±∞}; integrals against signed measures → EReal sSup/sInf; Jordan decomposition ∫ g dϕ⁺ − ∫ g dϕ⁻; reason: Lean convention; same instances
-- source:
--   Guo, Wang, A moment-SOS hierarchy for robust polynomial matrix inequality optimization with SOS-convexity, arXiv:2304.12628v5, p. 18, Theorem 4.3

import Mathlib
import Definitions.Def_RobustPMI_Hierarchy_Model
import Definitions.Def_RobustPMI_Hierarchy_Supplement_Model

namespace RobustPMI.Hierarchy.Supplement

open MvPolynomial Matrix Filter Topology

/-- Theorem 4.3 (p. 18): under Assumptions 1 and 3 (and the standing assumption of p. 2 that
(RPMIO) has an optimizer), the values of the conic programs (4.2) and (4.3) both equal `f⋆`:
`f̃ = f̂ = f⋆`. -/
theorem theorem_4_3 {ℓ n m q s : ℕ} (f : MvPolynomial (Fin ℓ) ℝ)
    (θ : Fin s → MvPolynomial (Fin ℓ) ℝ)
    (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ))
    (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ))
    (hP : P.IsSymm) (hG : G.IsSymm)
    (h1 : Assumption1 f θ P G) (h3 : Assumption3 θ P G)
    (hmin : ∃ y, IsGlobalMin f θ P G y) :
    ftilde f θ P G = (fstar f θ P G : EReal) ∧ fhat f θ P G = (fstar f θ P G : EReal) := by sorry

end RobustPMI.Hierarchy.Supplement
