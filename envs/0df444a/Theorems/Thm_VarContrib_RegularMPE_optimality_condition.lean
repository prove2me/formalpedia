-- Prove2me | Theorems.Thm_VarContrib_RegularMPE_optimality_condition
-- name    : VarContrib.RegularMPE.optimality_condition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:13:49.887005+00:00
-- url     : https://prove2.me/theorems/f74916cd-619c-44b1-9ea4-7d486a1e9c66
-- title:
--   §2.2 optimality condition, p. 10, for V of (4) against a regular opponent rate (as applied on p. 38) — (i)–(ii) make V the value over Ξ
-- statement:
--   Assume the standing assumptions and Assumptions 1–3. Let $\theta\in I$ and $A$ be such that $V$ of (4) is $C^2$ on $I$, and let the opponent contribute at a rate $u_j\in\mathcal U$, nonnegative on $I$. Write
--   $$\mathcal A^{\xi_j}=\tfrac12\sigma(x)^2\partial_x^2+[\mu(x)+u_j(x)]\partial_x-r .$$
--   Suppose that (i) $\mathcal A^{\xi_j}V(x)+\pi(x)\le0$ and $V'(x)-k\le0$ for all $x\in I$, and (ii) $[\mathcal A^{\xi_j}V(x)+\pi(x)][V'(x)-k]=0$ for all $x\in I$. Then for every $x\in I$:
--
--   1. every admissible control $\zeta$ and every solution $Z$ of $dZ_t=[\mu+u_j](Z_t)dt+\sigma(Z_t)dW_t+d\zeta_t$, $Z_{0-}=x$, satisfy
--   $$\mathbb E\Big[\int_0^\infty e^{-rt}\pi(Z_t)dt-\int_{[0,\infty)}e^{-rt}k\,d\zeta_t\Big]\le V(x);$$
--   2. every admissible control that reflects such a $Z$ upward at $\theta$ attains $V(x)$.
--
--   So $V$ is the optimal value $\sup_{\zeta\in\Xi}$ of the player facing the opponent's rate. The proof of Theorem 2 uses it to pass from best response within $\Sigma_i$ to best response within all of $\Xi_i$.
--
--   **Formalization Note.** The paper states the condition for an arbitrary $V\in C^2(I)$ and $\mathcal A$; in that generality it is false ($V(x)=kx+c$ with $c$ large satisfies (i)–(ii) on $I=\mathbb R$ but is unbounded, while the value is at most $\pi_M/r$). It is posed for $V$ of the form (4), the only form the paper applies it to, with the operator $\mathcal A^{\xi_j}$ of p. 38; $u_j=0$ gives the single decision maker's case. "Coincides with the optimal solution" is posed as an upper bound over admissible controls plus attainment by every admissible reflecting control at $\theta$.
-- source:
--   Kwon, Game of Variable Contributions to the Common Good under Uncertainty, arXiv:1904.00500v1, p. 10, §2.2 optimality condition (before Lemma 1), as applied in Appendix A, proof of Theorem 2, p. 38

import Mathlib
import Definitions.Def_VarContrib_RegularMPE_Model
import Definitions.Def_VarContrib_RegularMPE_Setting
import Definitions.Def_VarContrib_RegularMPE_Game

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace VarContrib.RegularMPE

/-- The optimality condition of §2.2 (Kwon, p. 10), for `V` of the form (4) and against an
opponent contributing at a regular feedback rate `u_j ≥ 0` (as applied in the proof of
Theorem 2, p. 38, with `𝒜^{ξ_j} = ½σ²∂²_x + (μ + u_j)∂_x − r`): if `V ∈ C²(I)` satisfies
(i) `𝒜^{ξ_j}V + π ≤ 0` and `V′ − k ≤ 0` on `I` and (ii) `[𝒜^{ξ_j}V + π][V′ − k] = 0` on `I`, then
from every `x ∈ I` every admissible control has payoff at most `V(x)`, and every admissible
control reflecting the state upward at `θ` has payoff exactly `V(x)`. -/
theorem optimality_condition {Ω : Type*} [MeasurableSpace Ω] (m : Model) (S : Setting Ω)
    (hst : Standing m S) (θ A : ℝ) (hθ : θ ∈ m.I)
    (hV : ContDiffOn ℝ 2 (Vsol m S θ A) m.I)
    (uj : ℝ → ℝ) (huj : InU m uj) (huj0 : ∀ y ∈ m.I, 0 ≤ uj y)
    (hi : ∀ x ∈ m.I,
      gen m (Vsol m S θ A) x + uj x * deriv (Vsol m S θ A) x + m.π x ≤ 0 ∧
        deriv (Vsol m S θ A) x - m.k ≤ 0)
    (hii : ∀ x ∈ m.I,
      (gen m (Vsol m S θ A) x + uj x * deriv (Vsol m S θ A) x + m.π x) *
        (deriv (Vsol m S θ A) x - m.k) = 0) :
    ∀ x ∈ m.I,
      (∀ ζ Z : ℝ≥0 → Ω → ℝ, IsStateSol m S (fun y => m.μ y + uj y) x ζ Z → Adm m S ζ Z →
        devPay m S ζ Z ≤ Vsol m S θ A x) ∧
      (∀ ζ Z : ℝ≥0 → Ω → ℝ, IsStateSol m S (fun y => m.μ y + uj y) x ζ Z → Adm m S ζ Z →
        ReflAt θ ζ Z → devPay m S ζ Z = Vsol m S θ A x) := by sorry

end VarContrib.RegularMPE
