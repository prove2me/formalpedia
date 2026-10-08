-- Prove2me | Theorems.Thm_SymBoolPCSP_LPRounding_convex_combination
-- name    : SymBoolPCSP.LPRounding.convex_combination
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:30:16.911376+00:00
-- url     : https://prove2.me/theorems/bca36388-f0ae-470f-866d-32d804f80467
-- title:
--   §3.2, proof, p. 14 — convex combinations of LP solutions are LP solutions
-- statement:
--   Let $\Gamma$ be a family of Boolean promise relations and $\Psi$ an instance with $n$ variables. Let $u^{(1)}, \dots, u^{(m)} \in \mathbb Q^n$ be solutions of the LP relaxation of §3.2 and let $\lambda_1, \dots, \lambda_m \ge 0$ be rationals with $\sum_k \lambda_k = 1$. Then
--   $$\sum_{k=1}^m \lambda_k\, u^{(k)}$$
--   is also a solution of the LP relaxation.
--
--   In the proof of correctness this is applied to the $n$ columns of the matrix $M$ of LP solutions found by the algorithm, so that $Mv$ is a solution for every probability vector $v$.
--
--   **Formalization Note** The paper states the fact for the $n$ columns of $M$; this item states the general convexity of the solution set over $\mathbb Q$, for any finite number $m$ of solutions.
-- source:
--   J. Brakensiek, V. Guruswami, Promise Constraint Satisfaction: Algebraic Structure and a Symmetric Boolean Dichotomy, arXiv:1704.01937v2, p. 14, §3.2, proof (second paragraph)

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_LPRounding_Basic

open PCSPBLPAff.Symmetric

namespace SymBoolPCSP.LPRounding

/-- §3.2, proof, p. 14: any convex combination of LP solutions is an LP solution. (The
paper applies this to the `n` columns of the matrix `M`; this is the general convexity.) -/
theorem convex_combination {τ : Type} {ar : τ → ℕ} (𝔸 : RelStruct τ ar Bool)
    (X : Instance τ ar) {m : ℕ} (u : Fin m → Fin X.n → ℚ) (hu : ∀ k, IsHullLPSol 𝔸 X (u k))
    (lam : Fin m → ℚ) (hlam0 : ∀ k, 0 ≤ lam k) (hlam1 : ∑ k, lam k = 1) :
    IsHullLPSol 𝔸 X (∑ k, lam k • u k) := by sorry

end SymBoolPCSP.LPRounding
