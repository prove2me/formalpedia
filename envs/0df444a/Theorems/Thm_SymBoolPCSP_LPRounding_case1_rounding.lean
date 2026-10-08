-- Prove2me | Theorems.Thm_SymBoolPCSP_LPRounding_case1_rounding
-- name    : SymBoolPCSP.LPRounding.case1_rounding
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:30:09.346754+00:00
-- url     : https://prove2.me/theorems/9baf7a33-37db-41a4-8007-b530055c265f
-- title:
--   §3.2, proof, Case 1, p. 14 — with $\mathrm{Maj}_L$ for all odd $L$, rounding an LP solution with no coordinate $1/2$ satisfies $\Psi_Q$
-- statement:
--   Let $\Gamma = \{(P_R, Q_R)\}$ be a finite family of Boolean promise relations ($P_R \subseteq Q_R$) such that $\mathrm{Maj}_L$ is a polymorphism of $\Gamma$ for every odd $L$. Let $\Psi = (\Psi_P, \Psi_Q)$ be an instance with $n$ variables and let $w \in \mathbb Q^n$ be a solution of the LP relaxation of §3.2 with $w_i \ne 1/2$ for all $i$. Then the rounded assignment
--   $$x^*_i = \lfloor w_i \rceil = \begin{cases} 1 & w_i > 1/2,\\ 0 & w_i < 1/2,\end{cases}$$
--   satisfies every clause of $\Psi_Q$.
--
--   Together with the Case 1 claim this gives soundness of the algorithm in the Majority case.
--
--   **Formalization Note** The conclusion states that, for every clause $j$, the tuple of rounded values of its scope lies in $Q_{R_j}$, i.e. the assignment `fun i => decide (1/2 < w i)` witnesses `SatIn X 𝔹`.
-- source:
--   J. Brakensiek, V. Guruswami, Promise Constraint Satisfaction: Algebraic Structure and a Symmetric Boolean Dichotomy, arXiv:1704.01937v2, p. 14, §3.2, proof, Case 1 (rounding claim x*_i = ⌊w_i⌉)

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_LPRounding_Basic

open PCSPBLPAff.Symmetric

namespace SymBoolPCSP.LPRounding

/-- §3.2, proof, Case 1, p. 14: if `Maj_L ∈ Pol(Γ)` for every odd `L` and `w` is a rational LP
solution with no coordinate equal to `1/2`, then rounding each `w_i` to the nearest integer,
`x*_i = ⌊w_i⌉`, satisfies `Ψ_Q`. -/
theorem case1_rounding {τ : Type} [Fintype τ] {ar : τ → ℕ} (𝔸 𝔹 : RelStruct τ ar Bool)
    (hPQ : ∀ R, 𝔸.rel R ⊆ 𝔹.rel R)
    (hMaj : ∀ L : ℕ, Odd L → IsPolymorphism 𝔸 𝔹 (SymBoolPCSP.CFixing.Maj L))
    (X : Instance τ ar) (w : Fin X.n → ℚ) (hw : IsHullLPSol 𝔸 X w)
    (hhalf : ∀ i, w i ≠ 1 / 2) :
    ∀ j : Fin X.m, (fun i => decide (1 / 2 < w i)) ∘ X.scope j ∈ 𝔹.rel (X.sym j) := by sorry

end SymBoolPCSP.LPRounding
