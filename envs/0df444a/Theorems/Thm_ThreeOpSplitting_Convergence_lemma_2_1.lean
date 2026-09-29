-- Prove2me | Theorems.Thm_ThreeOpSplitting_Convergence_lemma_2_1
-- name    : ThreeOpSplitting.Convergence.lemma_2_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:48:08.145406+00:00
-- url     : https://prove2.me/theorems/efa5d898-be63-4584-b6ab-19c7ecfe3095
-- title:
--   Lemma 2.1 — the points of Fig. 1 and the identities for $T$
-- statement:
--   Let $H$ be a real Hilbert space, $A, B : H \to 2^H$ maximal monotone, $C : H \to H$ $\beta$-cocoercive with $\beta > 0$, $\gamma > 0$, and let $J_A = J_{\gamma A}$, $J_B = J_{\gamma B}$ be the resolvents. Let $T$ be the operator of Eq. (1.2). For $z \in H$ define
--   $$x_B := J_B(z),\quad z' := 2x_B - z,\quad z'' := z' - \gamma C x_B,\quad x_A := J_A(z''),$$
--   $$u_B := \gamma^{-1}(z - x_B),\qquad u_A := \gamma^{-1}(z'' - x_A).$$
--   Then $u_B \in Bx_B$, $u_A \in Ax_A$, and
--   $$Tz - z = x_A - x_B = -\gamma\,(u_B + u_A + Cx_B), \qquad Tz = x_A + \gamma u_B.$$
--
--   These identities express one application of $T$ through a backward step on $B$, a forward step on $C$ and a backward step on $A$; the subgradient-like vectors $u_A, u_B$ are used throughout the convergence analysis.
--
--   **Formalization Note** The paper writes "Let $z \in H$" and then uses $z^k$; the statement is for an arbitrary point $z$. The standing assumptions of Section 1 (maximal monotone $A$, $B$; cocoercive $C$) are kept as hypotheses although the identities use only the resolvent inclusions and $\gamma > 0$.
-- source:
--   Davis and Yin, A Three-Operator Splitting Scheme and its Optimization Applications, Set-Valued Var. Anal. 25 (2017), https://doi.org/10.1007/s11228-017-0421-z, p. 832, Lemma 2.1

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_ThreeOpSplitting_Convergence_ThreeOperatorIteration

namespace ThreeOpSplitting.Convergence

/-- Davis–Yin, Lemma 2.1 (p. 832): the points of Fig. 1 and the identities for `T`. -/
theorem lemma_2_1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A B : H → Set H) (C : H → H) (β γ : ℝ) (JA JB : H → H)
    (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    (hβ : 0 < β) (hC : IsCocoercive β C) (hγ : 0 < γ)
    (hJA : IsResolvent γ A JA) (hJB : IsResolvent γ B JB) (z : H) :
    let xB := JB z
    let z' := (2 : ℝ) • xB - z
    let z'' := z' - γ • C xB
    let xA := JA z''
    let uB := γ⁻¹ • (z - xB)
    let uA := γ⁻¹ • (z'' - xA)
    uB ∈ B xB ∧ uA ∈ A xA ∧
      threeOp γ JA JB C z - z = xA - xB ∧
      xA - xB = -(γ • (uB + uA + C xB)) ∧
      threeOp γ JA JB C z = xA + γ • uB := by sorry

end ThreeOpSplitting.Convergence
