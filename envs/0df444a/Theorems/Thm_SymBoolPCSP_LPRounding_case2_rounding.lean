-- Prove2me | Theorems.Thm_SymBoolPCSP_LPRounding_case2_rounding
-- name    : SymBoolPCSP.LPRounding.case2_rounding
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:30:20.200979+00:00
-- url     : https://prove2.me/theorems/6bfc1d89-f1b8-4f35-8b31-34c0e68b849d
-- title:
--   §3.2, proof, Case 2, p. 15 — with $\mathrm{AT}_L$ for all odd $L$, comparing two LP solutions $w$, $\hat w$ satisfies $\Psi_Q$
-- statement:
--   Let $\Gamma = \{(P_R, Q_R)\}$ be a finite family of Boolean promise relations ($P_R \subseteq Q_R$) such that $\mathrm{AT}_L$ is a polymorphism of $\Gamma$ for every odd $L$. Let $\Psi = (\Psi_P, \Psi_Q)$ be an instance with $n$ variables, and let $w, \hat w \in \mathbb Q^n$ be solutions of the LP relaxation of §3.2 such that $w_i = \hat w_i$ only when $\hat w_i \in \{0,1\}$. Then the assignment
--   $$x^*_i = \begin{cases} 0 & w_i < \hat w_i \text{ or } w_i = \hat w_i = 0,\\ 1 & w_i > \hat w_i \text{ or } w_i = \hat w_i = 1,\end{cases}$$
--   satisfies every clause of $\Psi_Q$.
--
--   Together with the Case 2 perturbation this gives soundness of the algorithm in the Alternating-Threshold case.
--
--   **Formalization Note** The assignment is `fun i => decide (ŵ i < w i ∨ (w i = ŵ i ∧ ŵ i = 1))`; under the hypothesis on coincidences it equals the two-case rule above. The conclusion states that, for every clause $j$, the assigned tuple of its scope lies in $Q_{R_j}$.
-- source:
--   J. Brakensiek, V. Guruswami, Promise Constraint Satisfaction: Algebraic Structure and a Symmetric Boolean Dichotomy, arXiv:1704.01937v2, p. 15, §3.2, proof, Case 2 (the assignment x* and its verification)

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_LPRounding_Basic

open PCSPBLPAff.Symmetric

namespace SymBoolPCSP.LPRounding

/-- §3.2, proof, Case 2, p. 15: if `AT_L ∈ Pol(Γ)` for every odd `L`, and `w`, `ŵ` are rational
LP solutions with `w_i = ŵ_i` only where `ŵ_i ∈ {0, 1}`, then `x*_i = 0` if `w_i < ŵ_i` or
`w_i = ŵ_i = 0`, and `x*_i = 1` if `w_i > ŵ_i` or `w_i = ŵ_i = 1`, satisfies `Ψ_Q`. -/
theorem case2_rounding {τ : Type} [Fintype τ] {ar : τ → ℕ} (𝔸 𝔹 : RelStruct τ ar Bool)
    (hPQ : ∀ R, 𝔸.rel R ⊆ 𝔹.rel R)
    (hAT : ∀ L : ℕ, Odd L → IsPolymorphism 𝔸 𝔹 (SymBoolPCSP.CFixing.AT L))
    (X : Instance τ ar) (w what : Fin X.n → ℚ) (hw : IsHullLPSol 𝔸 X w)
    (hwhat : IsHullLPSol 𝔸 X what) (hcoinc : ∀ i, w i = what i → what i = 0 ∨ what i = 1) :
    ∀ j : Fin X.m,
      (fun i => decide (what i < w i ∨ (w i = what i ∧ what i = 1))) ∘ X.scope j ∈
        𝔹.rel (X.sym j) := by sorry

end SymBoolPCSP.LPRounding
