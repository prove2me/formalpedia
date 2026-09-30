-- Prove2me | Theorems.Thm_PolyhedralSOC_LowerBound_ball_sandwich
-- name    : PolyhedralSOC.LowerBound.ball_sandwich
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T20:48:02.079208+00:00
-- url     : https://prove2.me/theorems/1f8da26d-606d-4d11-9458-d8aacfc61924
-- title:
--   Proposition 3.1, proof — $B\subseteq G\subseteq(1+\varepsilon)B$
-- statement:
--   Let $\varepsilon>0$ and let $\Pi:\mathbb R^k\times\mathbb R\times\mathbb R^p\to\mathbb R^q$ be a polyhedral $\varepsilon$-approximation of $L^k$. Let
--   $$G=\{y\in\mathbb R^k\mid \Pi(y,1,u)\ge0\ \text{for some } u\}$$
--   and let $B=\{y\mid \|y\|_2\le 1\}$ be the closed unit Euclidean ball of $\mathbb R^k$. Then
--   $$B\subseteq G\subseteq (1+\varepsilon)B=\{y\mid \|y\|_2\le 1+\varepsilon\}.$$
--
--   This is the entry point of the lower-bound argument: the slice $G$ of the approximating polyhedral cone is squeezed between two concentric Euclidean balls whose radii differ by the factor $1+\varepsilon$.
--
--   **Formalization Note** The page writes "polyhedral $\alpha$ approximation" at this point, a misprint for $\varepsilon$.
-- source:
--   Ben-Tal & Nemirovski, On Polyhedral Approximations of the Second-Order Cone, Math. Oper. Res. 26(2):193–205 (2001), p. 202, Proposition 3.1, proof ("the set G contains the unit k-dimensional Euclidean ball B and is contained in the ball (1+ε)B")

import Mathlib
import Definitions.Def_PolyhedralSOC_Shared_LorentzCone
import Definitions.Def_PolyhedralSOC_Shared_IsPolyhedralApprox
import Definitions.Def_PolyhedralSOC_LowerBound_ProofObjects

namespace PolyhedralSOC.LowerBound

/-- Ben-Tal & Nemirovski, *On Polyhedral Approximations of the Second-Order Cone*,
Math. Oper. Res. 26(2):193–205 (2001), Proposition 3.1, proof, p. 202 (PDF p. 10):
"Since Π(·) is a polyhedral ε approximation of L^k, the set G contains the unit k-dimensional
Euclidean ball B and is contained in the ball (1+ε)B" (the page prints "α" for "ε"), where
`G = {y | Π(y, 1, u) ≥ 0 for some u}`. -/
theorem ball_sandwich {k p q : ℕ} {ε : ℝ} (hε : 0 < ε)
    (P : (Fin k → ℝ) × ℝ × (Fin p → ℝ) →ₗ[ℝ] (Fin q → ℝ))
    (hP : Shared.IsPolyhedralApprox k p q ε P) :
    {y : Fin k → ℝ | Shared.eucNorm y ≤ 1} ⊆ sliceG P ∧
      sliceG P ⊆ {y : Fin k → ℝ | Shared.eucNorm y ≤ 1 + ε} := by sorry

end PolyhedralSOC.LowerBound
