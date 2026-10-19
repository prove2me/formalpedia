-- Prove2me | Theorems.Thm_VarContrib_RegularMPE_lemma_1
-- name    : VarContrib.RegularMPE.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:13:42.932247+00:00
-- url     : https://prove2.me/theorems/0a9c545f-4bac-486d-91b8-062e9ee9952d
-- title:
--   Lemma 1, p. 10 — there are θ ∈ I and A such that V of (4) is C² on I and is the single decision maker's optimal value
-- statement:
--   Assume the standing assumptions and Assumptions 1–3. Then there exist a threshold $\theta\in I$ and a coefficient $A$ such that the function
--   $$V(x)=\begin{cases}k(x-\theta)+V(\theta) & x<\theta,\\ (R\pi)(x)+A\varphi(x) & x\ge\theta,\end{cases}\tag{4}$$
--   is twice continuously differentiable on $I$ and is the optimal value of the single decision maker: for every $x\in I$,
--
--   1. every admissible control $\zeta$ and every solution $Z$ of $dZ_t=\mu(Z_t)dt+\sigma(Z_t)dW_t+d\zeta_t$, $Z_{0-}=x$, satisfy
--   $$\mathbb E\Big[\int_0^\infty e^{-rt}\pi(Z_t)dt-\int_{[0,\infty)}e^{-rt}k\,d\zeta_t\Big]\le V(x);$$
--   2. every admissible control that reflects such a $Z$ upward at $\theta$ attains $V(x)$.
--
--   This is the monotone-follower benchmark; its value $V$ and threshold $\theta$ reappear unchanged in the equilibrium of Theorem 2.
--
--   **Formalization Note.** "The optimal solution" is posed as an upper bound over all admissible controls together with attainment by every admissible reflecting control on every solution of the state equation; the existence of the reflected solution is taken from SDE theory in the paper and is not posed.
-- source:
--   Kwon, Game of Variable Contributions to the Common Good under Uncertainty, arXiv:1904.00500v1, p. 10, Lemma 1, (4)

import Mathlib
import Definitions.Def_VarContrib_RegularMPE_Model
import Definitions.Def_VarContrib_RegularMPE_Setting
import Definitions.Def_VarContrib_RegularMPE_Game

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace VarContrib.RegularMPE

/-- Lemma 1 (Kwon, p. 10): under Assumptions 1–3 there are a threshold `θ ∈ I` and a
coefficient `A` such that `V` of (4) is `C²` on `I` and is the optimal value of the single
decision maker: from every `x ∈ I`, every admissible control has payoff at most `V(x)`, and
every admissible control reflecting the state upward at `θ` has payoff exactly `V(x)`. -/
theorem lemma_1 {Ω : Type*} [MeasurableSpace Ω] (m : Model) (S : Setting Ω)
    (hst : Standing m S) :
    ∃ θ ∈ m.I, ∃ A : ℝ, ContDiffOn ℝ 2 (Vsol m S θ A) m.I ∧ ∀ x ∈ m.I,
      (∀ ζ Z : ℝ≥0 → Ω → ℝ, IsStateSol m S m.μ x ζ Z → Adm m S ζ Z →
        devPay m S ζ Z ≤ Vsol m S θ A x) ∧
      (∀ ζ Z : ℝ≥0 → Ω → ℝ, IsStateSol m S m.μ x ζ Z → Adm m S ζ Z → ReflAt θ ζ Z →
        devPay m S ζ Z = Vsol m S θ A x) := by sorry

end VarContrib.RegularMPE
