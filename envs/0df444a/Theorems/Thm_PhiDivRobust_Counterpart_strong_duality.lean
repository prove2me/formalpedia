-- Prove2me | Theorems.Thm_PhiDivRobust_Counterpart_strong_duality
-- name    : PhiDivRobust.Counterpart.strong_duality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T18:51:20.325872+00:00
-- url     : https://prove2.me/theorems/0c5d62d4-38bd-45cd-82a5-e4d5ba809667
-- title:
--   Proof of Theorem 1, duality step (only if): strong duality with attainment for the worst-case problem
-- statement:
--   Let $\phi$ be a φ-divergence function and let $a\in\mathbb R^n$, $B\in\mathbb R^{n\times m}$, $\beta\in\mathbb R$, $C\in\mathbb R^{k\times m}$, $d\in\mathbb R^k$, $q\in\mathbb R^m$ with $q_i>0$ for all $i$, and $\rho>0$ be such that $q\in U$, where
--
--   $$U=\{p\in\mathbb R^m\mid p\ge0,\ Cp\le d,\ I_\phi(p,q)\le\rho\}.$$
--
--   Let $x\in\mathbb R^n$ satisfy $(a+Bp)^\top x\le\beta$ for all $p\in U$. Then there exist $\lambda\ge0$ and $\eta\in\mathbb R^k$, $\eta\ge0$, such that
--
--   $$g(\lambda,\eta)\le\beta,$$
--
--   where $g(\lambda,\eta)=\sup_{p\ge0}L(p,\lambda,\eta)$ is the dual objective function of the worst-case problem.
--
--   The point $q$ is regular in the paper's sense ($Cq\le d$ and $I_\phi(q,q)=0<\rho$), and this is what the paper invokes for the absence of a duality gap and for the attainment of the dual minimum; it is the heart of Theorem 1.
--
--   **Formalization Note** The conclusion is the existence of a dual pair, i.e. the paper's "the min is attained" form, not the weaker $\inf_{\lambda,\eta\ge0} g\le\beta$. $q>0$ replaces the printed $q\ge0$.
-- source:
--   Ben-Tal, den Hertog, De Waegenaere, Melenberg, Rennen, Robust Solutions of Optimization Problems Affected by Uncertain Probabilities, Management Sci. 59(2), 2013, p. 347, proof of Theorem 1, duality step (bottom of the left column to the top of the right column), the 'only if' direction

import Mathlib
import Definitions.Def_PhiDivRobust_Counterpart_IsPhiDivergenceFunction
import Definitions.Def_PhiDivRobust_Counterpart_uncertaintySet
import Definitions.Def_PhiDivRobust_Counterpart_dualFunction
open Matrix

namespace PhiDivRobust.Counterpart

/-- Ben-Tal et al. 2013, p. 347, proof of Theorem 1, duality step, the "only if" direction (strong
duality with attainment): since `q ∈ U` makes `U` regular (`Cq ≤ d`, `I_φ(q, q) = 0 < ρ`), if `x`
satisfies the robust constraint (11) over (12), then `g(λ, η) ≤ β` for some `λ ≥ 0` and `η ≥ 0`. -/
theorem strong_duality {n m k : ℕ} (φ : ℝ → EReal) (hφ : IsPhiDivergenceFunction φ)
    (a : Fin n → ℝ) (B : Matrix (Fin n) (Fin m) ℝ) (β : ℝ) (C : Matrix (Fin k) (Fin m) ℝ)
    (d : Fin k → ℝ) (q : Fin m → ℝ) (ρ : ℝ) (hq : ∀ i, 0 < q i) (hρ : 0 < ρ)
    (hqU : q ∈ uncertaintySet φ C d q ρ) (x : Fin n → ℝ)
    (h : ∀ p ∈ uncertaintySet φ C d q ρ, (a + B *ᵥ p) ⬝ᵥ x ≤ β) :
    ∃ lam : ℝ, ∃ η : Fin k → ℝ, 0 ≤ lam ∧ 0 ≤ η ∧
      dualFunction φ a B C d q ρ x lam η ≤ (β : EReal) := by sorry

end PhiDivRobust.Counterpart
