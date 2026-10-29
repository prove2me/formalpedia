-- Prove2me | Theorems.Thm_PutermanMDP_Multichain_laurent_improvement
-- name    : PutermanMDP.Multichain.laurent_improvement
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T03:00:23.757793+00:00
-- url     : https://prove2.me/theorems/8d531789-7a6f-4a44-8849-43b45ef3aa1e
-- title:
--   Lemma 9.2.1 — Laurent expansion of a policy improvement
-- statement:
--   Let $d,\delta$ be admissible deterministic Markov decision rules in the finite model, and define $w_\lambda(\delta,d)=r_\delta+\lambda P_\delta v_\lambda^{d^\infty}-v_\lambda^{d^\infty}$. For $0\le\lambda<1$:
--
--   1. $(I-\lambda P_\delta)^{-1}w_\lambda(\delta,d)=v_\lambda^{\delta^\infty}-v_\lambda^{d^\infty}$.
--   2. If $\delta(s)=d(s)$ then $w_\lambda(\delta,d)(s)=0$.
--   3. The expansion is
--   $$w_\lambda(\delta,d)=\frac{(P_\delta-I)g^{d^\infty}}{1-\lambda}+\bigl[r_\delta-g^{d^\infty}+(P_\delta-I)h^{d^\infty}\bigr]+f(\lambda),\qquad f(\lambda)\longrightarrow0\quad(\lambda\uparrow1).$$
--   This relates a single decision-rule switch to discounted value differences and the stationary gain and canonical bias.
--
--   **Formalization Note** The finite state/action hypothesis is the chapter's standing assumption on p. 442. The residual $f$ is explicitly defined as the difference between the two sides, and its vector convergence expresses the entire third clause. The matrix inverse is used in its nonsingular discount range. Finding F4 records an error in the printed third clause: in a two-state stay/exit model the stated residual is constantly (1,0), not tending to zero. The faithful statement retains the printed constant term; its conjunction is therefore expected to be disproved. Parts (1) and (2) are unchanged.
-- source:
--   Puterman, Markov Decision Processes: Discrete Stochastic Dynamic Programming, Wiley, 1994, https://doi.org/10.1002/9780470316887, p. 456 (PDF 472), Lemma 9.2.1; standing finiteness p. 442 (PDF 458)

import Mathlib
import Definitions.Def_PutermanMDP_Multichain_Criteria

open MarkovDecisionProcesses Filter
open scoped Topology Matrix

namespace PutermanMDP.Multichain

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq A] [Nonempty S]

/-- Lemma 9.2.1, p. 456 (PDF 472), all three parts. The last clause states
that the explicit residual in (9.2.11) tends to zero from the left. -/
theorem laurent_improvement [DecidableEq S] (M : StationaryMDP S A) (δ d : Rule M) :
    (∀ lam : ℝ, 0 ≤ lam → lam < 1 →
      (1 - lam • Matrix.of (transMatrix M δ.val))⁻¹ *ᵥ advantage M δ d lam =
        discounted M δ lam - discounted M d lam) ∧
    (∀ (lam : ℝ) (s : S), 0 ≤ lam → lam < 1 → δ.val s = d.val s →
      advantage M δ d lam s = 0) ∧
    Filter.Tendsto (residual M δ d) (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0) := by sorry

end PutermanMDP.Multichain
