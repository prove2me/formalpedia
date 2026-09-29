-- Prove2me | Theorems.Thm_ThreeOpSplitting_Convergence_lemma_2_2
-- name    : ThreeOpSplitting.Convergence.lemma_2_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:48:32.617274+00:00
-- url     : https://prove2.me/theorems/1c3e6d8d-5061-4e21-a1e3-595e5bdad03c
-- title:
--   Lemma 2.2 — fixed-point encoding: $\mathrm{zer}(A+B+C) = J_{\gamma B}(\mathrm{Fix}\,T)$
-- statement:
--   Let $H$ be a real Hilbert space, $A, B : H \to 2^H$ maximal monotone, $C : H \to H$ $\beta$-cocoercive with $\beta > 0$, $\gamma > 0$, and $J_A = J_{\gamma A}$, $J_B = J_{\gamma B}$ the resolvents. Let $T = J_A \circ (2J_B - I - \gamma C \circ J_B) + I - J_B$ be the operator of Eq. (1.2). Then
--   $$\operatorname{zer}(A + B + C) = J_B(\operatorname{Fix} T),$$
--   and
--   $$\operatorname{Fix} T = \{x + \gamma u : 0 \in (A + B + C)x,\ u \in Bx \cap (-Ax - Cx)\},$$
--   where $-Ax - Cx = \{-a - Cx : a \in Ax\}$.
--
--   The lemma reduces the inclusion problem (1.1) to a fixed-point problem for $T$: a zero of $A + B + C$ is recovered from any fixed point $z^*$ of $T$ as $J_B(z^*)$.
-- source:
--   Davis and Yin, A Three-Operator Splitting Scheme and its Optimization Applications, Set-Valued Var. Anal. 25 (2017), https://doi.org/10.1007/s11228-017-0421-z, p. 832, Lemma 2.2 (Fixed-point encoding)

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_ThreeOpSplitting_Convergence_ThreeOperatorIteration

namespace ThreeOpSplitting.Convergence

/-- Davis–Yin, Lemma 2.2 (Fixed-point encoding), p. 832:
`zer(A + B + C) = J_{γB}(Fix T)` and
`Fix T = {x + γ u | 0 ∈ (A + B + C) x, u ∈ B x ∩ (-A x - C x)}`. -/
theorem lemma_2_2 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A B : H → Set H) (C : H → H) (β γ : ℝ) (JA JB : H → H)
    (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    (hβ : 0 < β) (hC : IsCocoercive β C) (hγ : 0 < γ)
    (hJA : IsResolvent γ A JA) (hJB : IsResolvent γ B JB) :
    zer (opSum A B C) = JB '' Function.fixedPoints (threeOp γ JA JB C) ∧
      Function.fixedPoints (threeOp γ JA JB C) =
        {z : H | ∃ x u : H, (0 : H) ∈ opSum A B C x ∧ u ∈ B x ∧
          (∃ a ∈ A x, u = -a - C x) ∧ z = x + γ • u} := by sorry

end ThreeOpSplitting.Convergence
