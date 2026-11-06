-- Prove2me | Theorems.Thm_PrimalDualLDR_Multistage_theorem_3_dual
-- name    : PrimalDualLDR.Multistage.theorem_3_dual
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-05T17:11:57.241925+00:00
-- url     : https://prove2.me/theorems/1d3493cb-5b21-415c-9841-cedd3bc5d135
-- title:
--   Theorem 3, dual part — $\mathcal{MSP}^l$ is equivalent to the linear program (4.6)
-- statement:
--   Consider the linear multistage stochastic program $\mathcal{MSP}$ of §4 with deterministic constraint matrices $A_{ts}$, $b_t(\xi^t) = B_tP_t\xi$, $c_t(\xi^t) = C_tP_t\xi$. Assume that $\mathbb P$ has a polyhedral support $\Xi = \{\xi : W\xi\ge h\}$ of the type (2.1), that $\mathbb E_t(\xi) = M_tP_t\xi$ $\mathbb P$-a.s. for all $t$, and that $\mathcal{MSP}$ is strictly feasible. Assume moreover $(\star)$: $k \ge 2$, or some row of $\hat W$ (a row of $W$ below the two rows of (2.1b)) is nonzero. Then the dual linear-decision-rule problem
--   $$\mathcal{MSP}^l:\ \min_{x_t\in\mathcal L^2_{k^t,n_t},\,s_t\in\mathcal L^2_{k^t,m_t}} \mathbb E\Big(\sum_t c_t(\xi^t)^\top x_t(\xi^t)\Big)\ \text{s.t.}\ \mathbb E\Big(\Big[\sum_s A_{ts}x_s(\xi^s) + s_t(\xi^t) - b_t(\xi^t)\Big][P_t\xi]^\top\Big) = 0,\ s_t(\xi^t)\ge 0\ \mathbb P\text{-a.s.}$$
--   has the same optimal value as the linear program
--   $$(4.6):\ \min \sum_t\operatorname{Tr}(P_tMP_t^\top C_t^\top X_t)\ \text{s.t.}\ \sum_s A_{ts}X_sP_sN_tP_t + S_tP_t = B_tP_t,\ \ (W - he_1^\top)MP_t^\top S_t^\top \ge 0\ \ \forall t,$$
--   where $M = \mathbb E(\xi\xi^\top)$ and $N_t = MP_t^\top(P_tMP_t^\top)^{-1}$.
--
--   Optimal values are infima in the extended reals. This is the second assertion of Theorem 3. The hypothesis $(\star)$ is not in the paper; it is the same repair as in the goal theorem `PrimalDualLDR.Multistage.theorem_3`, whose formalization note explains that without it the assertion fails for $k = 1$ (the cone $\mathcal K$ of Proposition 3 becomes all of $\mathbb R$).
-- source:
--   Kuhn, Wiesemann, Georghiou, Primal and dual linear decision rules in stochastic and robust optimization, Optimization Online 2009/02/2218, p. 22, Theorem 3 (second assertion: MSP^l is equivalent to (4.6)); derivation pp. 20-22 (Lemmas 2, 3, (4.5)-(4.7)), parallel to the proof of Theorem 1 / (2.8), pp. 7-10

import Mathlib
import Definitions.Def_PrimalDualLDR_Multistage_Basic
import Definitions.Def_PrimalDualLDR_Multistage_Setting
import Definitions.Def_PrimalDualLDR_Multistage_Problems

open MeasureTheory Matrix

namespace PrimalDualLDR.Multistage

/-- Theorem 3 (p. 22), second assertion: assume that `P` has a polyhedral support of the type (2.1),
while `𝔼_t(ξ) = M_t P_t ξ` almost surely, and that `𝓜𝒮𝒫` is strictly feasible. Under the repair
hypothesis `2 ≤ k ∨ Ŵ ≠ 0` (see the goal theorem `theorem_3`), the dual linear-decision-rule problem
`𝓜𝒮𝒫^l` and the linear program (4.6) have the same optimal value. -/
theorem theorem_3_dual (σ : Setting) (hσ : σ.Standing) (hM : σ.LinearCondMean)
    (hsf : σ.StrictlyFeasible) (hW : 2 ≤ σ.k ∨ ∃ i : Fin σ.l, 2 ≤ i.val ∧ σ.W i ≠ 0) :
    σ.valMSPl = σ.valLP46 := by sorry

end PrimalDualLDR.Multistage
