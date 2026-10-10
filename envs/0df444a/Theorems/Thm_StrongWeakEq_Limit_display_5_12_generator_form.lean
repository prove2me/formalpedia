-- Prove2me | Theorems.Thm_StrongWeakEq_Limit_display_5_12_generator_form
-- name    : StrongWeakEq.Limit.display_5_12_generator_form
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T23:34:49.516286+00:00
-- url     : https://prove2.me/theorems/e5281640-152d-4aea-931e-c84dcd69d7b0
-- title:
--   Proof of Theorem 5.2, p. 18 — (5.12) divided by δₙ: f(0,i,Qⁿᵢ) + H·Qⁿᵢ ≥ f(0,i,Q^{u,n}ᵢ) + H·Q^{u,n}ᵢ
-- statement:
--   Fix a mesh $\delta>0$, a payoff $f$, a vector $H\in\mathbb R^N$, a state $i$ and two matrices $u,u^n$. Write $Q^{u,n}=\frac1\delta(u-I)$ and $Q^n=Q^{u^n,n}$ as in (5.10), and $\kappa^n(0,i,\alpha)=f\big(0,i,\tfrac1\delta(\alpha-e_i)\big)\,\delta$ as in (5.9). Then
--
--   $$
--   \kappa^n(0,i,u^n_i)+H\cdot u^n_i\ \ge\ \kappa^n(0,i,u_i)+H\cdot u_i
--   \quad\Longleftrightarrow\quad
--   f(0,i,Q^n_i)+H\cdot Q^n_i\ \ge\ f(0,i,Q^{u,n}_i)+H\cdot Q^{u,n}_i .
--   $$
--
--   Applied with $H=H^n(u^n)$, this turns the discrete one-step inequality (5.12) into an inequality between generator rows, which is the form in which the proof of Theorem 5.2 lets $\delta_n\downarrow0$; the limit is the first-order condition (3.10).
--
--   **Formalization Note** The equivalence is stated for arbitrary real matrices $u,u^n$ and vectors $H$: it is pure algebra ($u_i=e_i+\delta\,Q^{u,n}_i$, so both sides differ by the common term $H_i$ and the factor $\delta>0$). States are `Fin N`.
-- source:
--   Huang & Zhou, Strong and Weak Equilibria for Time-Inconsistent Stochastic Control in Continuous Time, arXiv:1809.09243v3, p. 18, proof of Theorem 5.2

import Mathlib
import Definitions.Def_StrongWeakEq_Existence_Model
import Definitions.Def_StrongWeakEq_Discrete_DiscreteModel
import Definitions.Def_StrongWeakEq_Limit_Discretization

namespace StrongWeakEq.Limit

/-- Proof of Theorem 5.2, p. 18: for a mesh `δ > 0` and any vector `H`, the one-step inequality
(5.12) between `u` and `uⁿ` is equivalent to its generator form
`f(0,i,Q^{uⁿ}ᵢ) + H·Q^{uⁿ}ᵢ ≥ f(0,i,Q^{u}ᵢ) + H·Q^{u}ᵢ` with `Q^{u} = (u − I)/δ`. -/
theorem display_5_12_generator_form {N : ℕ} (f : ℝ → Fin N → (Fin N → ℝ) → ℝ)
    (δ : ℝ) (hδ : 0 < δ) (H : Fin N → ℝ) (u un : Matrix (Fin N) (Fin N) ℝ) (i : Fin N) :
    (kappaN f δ 0 i (u i) + H ⬝ᵥ u i ≤ kappaN f δ 0 i (un i) + H ⬝ᵥ un i) ↔
      (f 0 i (genOf δ u i) + H ⬝ᵥ genOf δ u i ≤ f 0 i (genOf δ un i) + H ⬝ᵥ genOf δ un i) := by sorry

end StrongWeakEq.Limit
