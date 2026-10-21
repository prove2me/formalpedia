-- Prove2me | Theorems.Thm_TechFinConstr_Selection_proposition_2
-- name    : TechFinConstr.Selection.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:50:17.900705+00:00
-- url     : https://prove2.me/theorems/760d4a72-6264-4d77-9b2e-bc2ecd5f2ce3
-- title:
--   Proposition 2, p. 15 — closed-form agency rent E_q[s*(p)]; slope 1/Φ_σ(m)(p); continuous, increasing, convex on [0, π]
-- statement:
--   In Starmans' model, let $p\in\mathscr P$, let $\sigma$ order the tranches so that $\Phi_{\sigma(1)}(p)\ge\dots\ge\Phi_{\sigma(n)}(p)$, and let $\bar c_0,\dots,\bar c_n$ be the thresholds of Proposition 1. Write $R(c)$ for the agency rent function, the common value of $\mathbb E_q[s]$ over the optimal contracts $s$ of problem (1) at disutility $c$. Then:
--
--   1. if $m\in\{1,\dots,n\}$ and $\bar c_{m-1}<c\le\bar c_m$, every optimal contract $s$ satisfies
--   $$\mathbb E_q[s]=\frac{c}{\Phi_{\sigma(m)}(p)}+\sum_{j=1}^{m-1}\bigl(x_{\sigma(j)}-x_{\sigma(j)-1}\bigr)\Bigl(1-\frac{\Phi_{\sigma(j)}(p)}{\Phi_{\sigma(m)}(p)}\Bigr)\sum_{i=\sigma(j)}^n q_i ;$$
--   2. for $\bar c_{m-1}<c<\bar c_m$, $R$ is differentiable at $c$ with $R'(c)=1/\Phi_{\sigma(m)}(p)>0$;
--   3. for every $c\in[0,\pi]$ an optimal contract exists, and every optimal contract $s$ has $\mathbb E_q[s]=R(c)$;
--   4. on $[0,\pi]$ the function $R$ is continuous, strictly increasing and convex.
--
--   Piecewise linearity is the content of item 1. The proposition is the complete description of agency rents used in the comparison of entrepreneurs (Proposition 6).
--
--   **Formalization Note.** $R$ is `agencyRent E p`, defined as the infimum of $\mathbb E_q[s]$ over the optimal contracts; item 3 states that on $[0,\pi]$ this infimum is attained by every optimal contract (footnote 7, p. 11: all optimal contracts have the same agency rent), so "an optimal contract from Proposition 1" is read as every optimal contract. "Increasing" is rendered as strictly increasing, as the proof (p. 41) and the positive slopes give. Indices of $\sigma$ and $m$ are shifted as in Proposition 1.
-- source:
--   Starmans, Technological Determinants of Financial Constraints, manuscript (February 4, 2022), p. 15, Proposition 2 (proof p. 41, Appendix A.8)

import Mathlib
import Definitions.Def_TechFinConstr_Selection_Model

namespace TechFinConstr.Selection

open Finset

theorem proposition_2 {n : ℕ} (E : Economy n) (hE : E.Standing) (p : Fin (n + 1) → ℝ) (hp : InP E p)
    (σ : Equiv.Perm (Fin n))
    (hσ : ∀ a b : Fin n, a ≤ b → Phi E p (σ b).succ ≤ Phi E p (σ a).succ) :
    (∀ (m : Fin n) (c : ℝ), cbar E p σ m.val < c → c ≤ cbar E p σ (m.val + 1) →
      ∀ s, IsOptimalContract E p c s →
        expect E.q s = c / Phi E p (σ m).succ +
          ∑ j ∈ univ.filter (fun j : Fin n => j.val < m.val),
            (E.x (σ j).succ - E.x (σ j).castSucc) *
              (1 - Phi E p (σ j).succ / Phi E p (σ m).succ) * tail E.q (σ j).succ) ∧
    (∀ (m : Fin n) (c : ℝ), cbar E p σ m.val < c → c < cbar E p σ (m.val + 1) →
      HasDerivAt (agencyRent E p) (1 / Phi E p (σ m).succ) c ∧ 0 < 1 / Phi E p (σ m).succ) ∧
    (∀ c ∈ Set.Icc 0 E.piE, (∃ s, IsOptimalContract E p c s) ∧
      ∀ s, IsOptimalContract E p c s → expect E.q s = agencyRent E p c) ∧
    ContinuousOn (agencyRent E p) (Set.Icc 0 E.piE) ∧
    StrictMonoOn (agencyRent E p) (Set.Icc 0 E.piE) ∧
    ConvexOn ℝ (Set.Icc 0 E.piE) (agencyRent E p) := by sorry

end TechFinConstr.Selection
