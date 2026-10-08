-- Prove2me | Theorems.Thm_PrimalDualLDR_Multistage_sec_4_eq_4_7
-- name    : PrimalDualLDR.Multistage.sec_4_eq_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:43:47.141489+00:00
-- url     : https://prove2.me/theorems/f978e099-aefb-40c9-96df-85f91be0512d
-- title:
--   §4, (4.7) — the equality constraints of 𝓜𝒮𝒫^l become those of (4.6)
-- statement:
--   Consider the multistage setting of §4 under its standing assumptions, with $M = \mathbb E(\xi\xi^\top)$ and $N_t := MP_t^\top(P_tMP_t^\top)^{-1}$. Fix a stage $t$.
--
--   1. Let $x_s \in \mathcal L^2_{k^s,n_s}$ ($s \in \mathbb T$) and $s_t \in \mathcal L^2_{k^t,m_t}$ be decision rules and $X_s \in \mathbb R^{n_s\times k^s}$, $S_t \in \mathbb R^{m_t\times k^t}$ matrices related by (4.3): $X_sP_sM = \mathbb E(x_s(\xi^s)\xi^\top)$ for every $s$, and $S_tP_tM = \mathbb E(s_t(\xi^t)\xi^\top)$. Then the $t$-th equality constraint of $\mathcal{MSP}^l$, $\mathbb E\big([\sum_s A_{ts}x_s(\xi^s) + s_t(\xi^t) - b_t(\xi^t)][P_t\xi]^\top\big) = 0$, holds if and only if
--   $$\sum_{s=1}^T A_{ts}X_sP_sMP_t^\top + S_tP_tMP_t^\top = B_tP_tMP_t^\top. \tag{4.7}$$
--   2. For all matrices $X_s$, $S_t$, (4.7) holds if and only if
--   $$\sum_{s=1}^T A_{ts}X_sP_sN_tP_t + S_tP_t = B_tP_t,$$
--   the $t$-th equality constraint of (4.6).
--
--   This is the step in the derivation of the linear program (4.6) where the multistage case differs from the one-stage case of §2.
--
--   **Formalization Note** The paper derives the forward direction of part 2 by multiplying (4.7) from the right by $(P_tMP_t^\top)^{-1}P_t$; the stated equivalence also contains the converse (multiply by $MP_t^\top$), which the reformulation of $\mathcal{MSP}^l$ as (4.6) needs. Invertibility of $P_tMP_t^\top$ is not a hypothesis: it follows from the standing assumptions ("$P_tMP_t^\top$ inherits invertibility from $M$"). $\mathcal{MSP}^l$'s equality constraint is in the corrected reading in which $\sum_s$ covers only $A_{ts}x_s(\xi^s)$.
-- source:
--   Kuhn, Wiesemann, Georghiou, Primal and dual linear decision rules in stochastic and robust optimization, Optimization Online 2009/02/2218, p. 21, §4, (4.3), (4.6), (4.7)

import Mathlib
import Definitions.Def_PrimalDualLDR_Multistage_Basic
import Definitions.Def_PrimalDualLDR_Multistage_Setting
import Definitions.Def_PrimalDualLDR_Multistage_Problems

open MeasureTheory Matrix

namespace PrimalDualLDR.Multistage

/-- §4, (4.7) (p. 21): the equality constraints of `𝓜𝒮𝒫^l` and of (4.6). Under the standing
assumptions of §4, for every stage `t`:
1. if the rules `x_s ∈ 𝓛²_{k^s,n_s}`, `s_t ∈ 𝓛²_{k^t,m_t}` and the matrices `X_s`, `S_t` are related by
   (4.3), i.e. `X_s P_s M = 𝔼(x_s(ξ^s) ξᵀ)` for all `s` and `S_t P_t M = 𝔼(s_t(ξ^t) ξᵀ)`, then the `t`-th
   equality constraint of `𝓜𝒮𝒫^l` holds iff (4.7):
   `Σ_s A_ts X_s P_s M P_tᵀ + S_t P_t M P_tᵀ = B_t P_t M P_tᵀ`;
2. for all matrices `X_s`, `S_t`, (4.7) holds iff the equality constraint of (4.6):
   `Σ_s A_ts X_s P_s N_t P_t + S_t P_t = B_t P_t`, where `N_t = M P_tᵀ (P_t M P_tᵀ)⁻¹`. -/
theorem sec_4_eq_4_7 (σ : Setting) (hσ : σ.Standing) (t : Fin σ.T) :
    (∀ (x : σ.XRules) (s : (Fin (σ.kb t) → ℝ) → (Fin (σ.m t) → ℝ)) (X : σ.XFam)
        (S : Matrix (Fin (σ.m t)) (Fin (σ.kb t)) ℝ),
        (∀ r, σ.IsL2RuleAt r (x r)) → σ.IsL2RuleAt t s →
        (∀ r, X r * σ.Pt r * σ.M = σ.moment r (x r)) → S * σ.Pt t * σ.M = σ.moment t s →
        (σ.eqMSPl t x s ↔
          ∑ r, σ.A t r * X r * σ.Pt r * σ.M * (σ.Pt t)ᵀ + S * σ.Pt t * σ.M * (σ.Pt t)ᵀ =
            σ.B t * σ.Pt t * σ.M * (σ.Pt t)ᵀ)) ∧
    (∀ (X : σ.XFam) (S : Matrix (Fin (σ.m t)) (Fin (σ.kb t)) ℝ),
        (∑ r, σ.A t r * X r * σ.Pt r * σ.M * (σ.Pt t)ᵀ + S * σ.Pt t * σ.M * (σ.Pt t)ᵀ =
            σ.B t * σ.Pt t * σ.M * (σ.Pt t)ᵀ) ↔
          ∑ r, σ.A t r * X r * σ.Pt r * σ.N t * σ.Pt t + S * σ.Pt t = σ.B t * σ.Pt t) := by sorry

end PrimalDualLDR.Multistage
