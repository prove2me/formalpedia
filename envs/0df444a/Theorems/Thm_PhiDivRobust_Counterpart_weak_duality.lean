-- Prove2me | Theorems.Thm_PhiDivRobust_Counterpart_weak_duality
-- name    : PhiDivRobust.Counterpart.weak_duality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T18:50:39.976989+00:00
-- url     : https://prove2.me/theorems/9d35e24d-0f0d-4656-bd38-ffe5d5cef6c1
-- title:
--   Proof of Theorem 1, duality step (if): g(λ, η) ≤ β for some λ, η ≥ 0 implies the robust constraint (11)
-- statement:
--   Let $\phi$ be a φ-divergence function and let $a\in\mathbb R^n$, $B\in\mathbb R^{n\times m}$, $\beta\in\mathbb R$, $C\in\mathbb R^{k\times m}$, $d\in\mathbb R^k$, $q\in\mathbb R^m$ with $q_i>0$ for all $i$, and $\rho>0$ be such that $q\in U$, where
--
--   $$U=\{p\in\mathbb R^m\mid p\ge0,\ Cp\le d,\ I_\phi(p,q)\le\rho\}.$$
--
--   Let $x\in\mathbb R^n$. If there are $\lambda\ge0$ and $\eta\in\mathbb R^k$, $\eta\ge0$, with $g(\lambda,\eta)\le\beta$, where $g$ is the dual objective function of the worst-case problem, then
--
--   $$(a+Bp)^\top x\le\beta\qquad\text{for all } p\in U.$$
--
--   This is the weak-duality half of the paper's statement that $x$ satisfies (11) if and only if $g(\lambda,\eta)\le\beta$ for some $\lambda\ge0$ and $\eta\ge0$.
--
--   **Formalization Note** The hypotheses are the standing assumptions of Theorem 1, with $q>0$ in place of the printed $q\ge0$; this direction does not need all of them.
-- source:
--   Ben-Tal, den Hertog, De Waegenaere, Melenberg, Rennen, Robust Solutions of Optimization Problems Affected by Uncertain Probabilities, Management Sci. 59(2), 2013, p. 347, proof of Theorem 1, duality step (bottom of the left column to the top of the right column), the 'if' direction

import Mathlib
import Definitions.Def_PhiDivRobust_Counterpart_IsPhiDivergenceFunction
import Definitions.Def_PhiDivRobust_Counterpart_uncertaintySet
import Definitions.Def_PhiDivRobust_Counterpart_dualFunction
open Matrix

namespace PhiDivRobust.Counterpart

/-- Ben-Tal et al. 2013, p. 347, proof of Theorem 1, duality step, the "if" direction (weak duality):
if `g(λ, η) ≤ β` for some `λ ≥ 0` and `η ≥ 0`, then `x` satisfies the robust constraint (11)
over the uncertainty region (12). -/
theorem weak_duality {n m k : ℕ} (φ : ℝ → EReal) (hφ : IsPhiDivergenceFunction φ)
    (a : Fin n → ℝ) (B : Matrix (Fin n) (Fin m) ℝ) (β : ℝ) (C : Matrix (Fin k) (Fin m) ℝ)
    (d : Fin k → ℝ) (q : Fin m → ℝ) (ρ : ℝ) (hq : ∀ i, 0 < q i) (hρ : 0 < ρ)
    (hqU : q ∈ uncertaintySet φ C d q ρ) (x : Fin n → ℝ)
    (h : ∃ lam : ℝ, ∃ η : Fin k → ℝ, 0 ≤ lam ∧ 0 ≤ η ∧
      dualFunction φ a B C d q ρ x lam η ≤ (β : EReal)) :
    ∀ p ∈ uncertaintySet φ C d q ρ, (a + B *ᵥ p) ⬝ᵥ x ≤ β := by sorry

end PhiDivRobust.Counterpart
