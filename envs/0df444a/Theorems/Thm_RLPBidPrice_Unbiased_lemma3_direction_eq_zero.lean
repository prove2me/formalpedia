-- Prove2me | Theorems.Thm_RLPBidPrice_Unbiased_lemma3_direction_eq_zero
-- name    : RLPBidPrice.Unbiased.lemma3_direction_eq_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T12:48:26.43499+00:00
-- url     : https://prove2.me/theorems/37585f35-10c8-4a59-a2c5-b311a4039a84
-- title:
--   Lemma 3 (corrected: C1 on [A I]) — a feasible direction d from μ_* with dᵀAʲ = 0 on E₀ ∪ E₁ and dᵀx = 0 is zero
-- statement:
--   Let $A$ be a 0/1 incidence matrix with nonzero columns, $r \ge 0$, $Y \ge 0$, and $x \ge 0$ satisfying Condition C1′ (whenever $x$ lies in the span of a set of columns of $[A\ I]$, that set spans $\mathbb{R}^m$). Let $\mu_*$ be an optimal dual price vector, i.e. a minimizer of $L(x, \cdot)$ over $\mu \ge 0$. Let $d \in \mathbb{R}^m$ be a feasible direction from $\mu_*$: for some $\epsilon > 0$,
--   $$\mu_* + h d \ge 0, \qquad h \in [0, \epsilon]. \tag{15}$$
--   Fix $h \in (0, \epsilon]$ and define
--   $$E_0 = \{j : r^j - \mu_*^\top A^j > 0\}, \tag{16}$$
--   $$E_1 = \{j : r^j - \mu_*^\top A^j = 0,\ r^j - \mu_*^\top A^j - h d^\top A^j > 0\}. \tag{17}$$
--   If $d^\top A^j = 0$ for all $j \in E_0 \cup E_1$ and $d^\top x = 0$, then $d = 0$.
--
--   In the paper this is the step showing that no nonzero feasible direction leaves $L(x, \cdot)$ constant, which is how uniqueness of $\mu_*$ is obtained.
--
--   **Formalization Note.** The context of Eqs. (15)–(17) — the optimal $\mu_*$, the feasible direction $d$ with its $\epsilon$, and the step $h$ used in $E_1$ — is carried as hypotheses. $d^\top A^j$ is written `d ⬝ᵥ (fun i => A i j)`.
--
--   **Correction.** The printed lemma assumes Condition 1 (only the columns of $A$); it is stated here under C1′ (the columns of $[A\ I]$). With the printed condition it is false: for $A$ with rows $(0,1,1), (1,1,0), (1,0,1)$, $r = (100,1,1)$, $x = (1,1,1)$ and $Y = (2, 1/2, 1/2)$ (for instance), $\mu_* = (0, 50, 50)$ is optimal and $d = (0, 1, -1)$ gives $E_0 = E_1 = \emptyset$ and $d^\top x = 0$ with $d \neq 0$, while Condition 1 holds at $x$.
-- source:
--   Talluri, van Ryzin, A Randomized Linear Programming Method for Computing Network Bid Prices, Transp. Sci. 33(2), 1999, p. 211, Lemma 3 with Eqs. (15)-(17)

import Mathlib
import Definitions.Def_RLPBidPrice_Unbiased_Model

open MeasureTheory Matrix

namespace RLPBidPrice.Unbiased

theorem lemma3_direction_eq_zero {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin n → ℝ)
    (hA : IsIncidence A) (hr : 0 ≤ r) (x : Fin m → ℝ) (hx : 0 ≤ x)
    (hC1 : ConditionOnePrime A x) (y₀ : Fin n → ℝ) (hy₀ : 0 ≤ y₀)
    (μs : Fin m → ℝ) (hμs : IsDualOpt A r x y₀ μs)
    (d : Fin m → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hfeas : ∀ h ∈ Set.Icc (0 : ℝ) ε, 0 ≤ μs + h • d)
    (h : ℝ) (hh : h ∈ Set.Ioc (0 : ℝ) ε)
    (E₀ E₁ : Set (Fin n))
    (hE₀ : E₀ = {j | r j - μs ⬝ᵥ (fun i => A i j) > 0})
    (hE₁ : E₁ = {j | r j - μs ⬝ᵥ (fun i => A i j) = 0 ∧
      r j - μs ⬝ᵥ (fun i => A i j) - h * d ⬝ᵥ (fun i => A i j) > 0})
    (hdA : ∀ j ∈ E₀ ∪ E₁, d ⬝ᵥ (fun i => A i j) = 0)
    (hdx : d ⬝ᵥ x = 0) :
    d = 0 := by sorry

end RLPBidPrice.Unbiased
