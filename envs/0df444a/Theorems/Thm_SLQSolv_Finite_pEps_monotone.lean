-- Prove2me | Theorems.Thm_SLQSolv_Finite_pEps_monotone
-- name    : SLQSolv.Finite.pEps_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:19:16.068533+00:00
-- url     : https://prove2.me/theorems/1e90fa0a-25db-4337-a95a-1aeb901ce876
-- title:
--   §5, proof of Theorem 5.3, (5.13), p. 2296 — P_ε(t) is nondecreasing in ε with lower bound P(t)
-- statement:
--   Let (H1)–(H2) and (5.6) hold, and for every $\varepsilon>0$ let $P_\varepsilon$ be the strongly regular solution of (5.7). Suppose Problem (SLQ)$^0$ is finite and let $P:[0,T]\to\mathbb S^n$ satisfy $V^0(t,x)=\langle P(t)x,x\rangle$ for all $(t,x)\in[0,T]\times\mathbb R^n$. Then for all $\varepsilon_2>\varepsilon_1>0$ and $t\in[0,T]$,
--
--   $$
--   P_{\varepsilon_2}(t)\ \ge\ P_{\varepsilon_1}(t)\ \ge\ P(t).
--   $$
--
--   Thus $\{P_\varepsilon(t)\}_{\varepsilon>0}$ is nondecreasing with lower bound $P(t)$, and therefore has a limit $\bar P(t)$ with
--
--   $$
--   \bar P(t)\equiv\lim_{\varepsilon\to0}P_\varepsilon(t)\ \ge\ P(t)\qquad\forall t\in[0,T]. \tag{5.13}
--   $$
--
--   This is the first step of the necessity part of Theorem 5.3.
--
--   **Formalization Note** Matrix inequalities are Loewner inequalities. The limit $\varepsilon\to0$ is the right limit $\varepsilon\downarrow0$ (`𝓝[>] 0`), since $P_\varepsilon$ is given for $\varepsilon>0$ only. $P(t)$ is required symmetric for $t\in[0,T]$ (the paper's $P:[0,T]\to\mathbb S^n$). The finiteness hypothesis is kept as the page states it, although the representation of $V^0$ already implies it.
-- source:
--   Sun–Li–Yong, SIAM J. Control Optim. 54 (2016), §5, proof of Theorem 5.3 (Necessity), chain before (5.13) and (5.13), p. 2296

import Mathlib
import Definitions.Def_SLQSolv_Finite_Riccati

open MeasureTheory Filter Topology Set
open scoped NNReal Matrix

namespace SLQSolv.Finite

theorem pEps_monotone {Ω : Type*} [MeasurableSpace Ω] {n m : ℕ} (Bs : Basis Ω) (d : Data Ω n m)
    (h1 : H1 Bs d) (h2 : H2 Bs d) (h56 : IsNonnegJ0 Bs d 0)
    (Pε : ℝ → ℝ≥0 → Matrix (Fin n) (Fin n) ℝ) (hPε : ∀ ε > 0, IsStronglyRegular (d.addR ε) (Pε ε))
    (hfin : IsFinite Bs d.hom)
    (P : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ) (hPsymm : ∀ t ≤ d.T, (P t).IsSymm)
    (hP : ∀ t ≤ d.T, ∀ x, V0 Bs d t x = (((P t *ᵥ x) ⬝ᵥ x : ℝ) : EReal)) :
    (∀ ε₁ ε₂ : ℝ, 0 < ε₁ → ε₁ < ε₂ → ∀ t ≤ d.T,
      (Pε ε₂ t - Pε ε₁ t).PosSemidef ∧ (Pε ε₁ t - P t).PosSemidef) ∧
    ∃ Pbar : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ, ∀ t ≤ d.T,
      Tendsto (fun ε => Pε ε t) (𝓝[>] 0) (𝓝 (Pbar t)) ∧ (Pbar t - P t).PosSemidef := by sorry

end SLQSolv.Finite
