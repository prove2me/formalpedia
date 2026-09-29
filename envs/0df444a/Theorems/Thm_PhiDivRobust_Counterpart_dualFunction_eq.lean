-- Prove2me | Theorems.Thm_PhiDivRobust_Counterpart_dualFunction_eq
-- name    : PhiDivRobust.Counterpart.dualFunction_eq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T18:50:05.56929+00:00
-- url     : https://prove2.me/theorems/b61819b7-ff87-41f9-926c-b1b277ee8c4f
-- title:
--   Eq. (15): the dual objective function separates over scenarios
-- statement:
--   Let $\phi$ be a φ-divergence function, $a\in\mathbb R^n$, $B\in\mathbb R^{n\times m}$, $C\in\mathbb R^{k\times m}$, $d\in\mathbb R^k$, $\rho\in\mathbb R$, $x\in\mathbb R^n$, and let $q\in\mathbb R^m$ with $q_i>0$ for all $i$. Write $b_i$ and $c_i$ for the $i$-th columns of $B$ and $C$. For every $\lambda\ge0$ and $\eta\in\mathbb R^k$ the dual objective function $g(\lambda,\eta)=\sup_{p\ge0}L(p,\lambda,\eta)$ satisfies
--
--   $$g(\lambda,\eta) = a^\top x + d^\top\eta + \rho\lambda + \sum_{i=1}^m q_i\,(\lambda\phi)^*\big(b_i^\top x - c_i^\top\eta\big),$$
--
--   where $(\lambda\phi)^*(s)=\sup_{t\ge0}\{st-\lambda\phi(t)\}$.
--
--   The maximization over $p$ decouples into $m$ one-dimensional problems, one per scenario, each of which is a scaled conjugate of $\phi$.
--
--   **Formalization Note** The identity holds in `EReal`. The paper's standing assumption is $q\ge0$; the change of variables $p_i = q_i t$ in the third equality of (15) needs $q_i>0$, which is assumed here (see the goal theorem for why $q\ge0$ is not enough).
-- source:
--   Ben-Tal, den Hertog, De Waegenaere, Melenberg, Rennen, Robust Solutions of Optimization Problems Affected by Uncertain Probabilities, Management Sci. 59(2), 2013, p. 347, Eq. (15)

import Mathlib
import Definitions.Def_PhiDivRobust_Counterpart_IsPhiDivergenceFunction
import Definitions.Def_PhiDivRobust_Counterpart_scaledConj
import Definitions.Def_PhiDivRobust_Counterpart_dualFunction
open Matrix

namespace PhiDivRobust.Counterpart

/-- Ben-Tal et al. 2013, p. 347, Eq. (15): for `q > 0`, `λ ≥ 0` and `η ∈ ℝᵏ`, the dual objective
function separates over scenarios,
`g(λ, η) = aᵀx + dᵀη + ρλ + ∑ᵢ qᵢ (λφ)*(bᵢᵀx − cᵢᵀη)`, where `bᵢ`, `cᵢ` are the `i`-th columns of
`B` and `C`. -/
theorem dualFunction_eq {n m k : ℕ} (φ : ℝ → EReal) (hφ : IsPhiDivergenceFunction φ)
    (a : Fin n → ℝ) (B : Matrix (Fin n) (Fin m) ℝ) (C : Matrix (Fin k) (Fin m) ℝ)
    (d : Fin k → ℝ) (q : Fin m → ℝ) (ρ : ℝ) (hq : ∀ i, 0 < q i) (x : Fin n → ℝ)
    (lam : ℝ) (hlam : 0 ≤ lam) (η : Fin k → ℝ) :
    dualFunction φ a B C d q ρ x lam η =
      ((a ⬝ᵥ x + d ⬝ᵥ η + ρ * lam : ℝ) : EReal) +
        ∑ i, (q i : EReal) *
          scaledConj φ lam ((fun j => B j i) ⬝ᵥ x - (fun j => C j i) ⬝ᵥ η) := by sorry

end PhiDivRobust.Counterpart
