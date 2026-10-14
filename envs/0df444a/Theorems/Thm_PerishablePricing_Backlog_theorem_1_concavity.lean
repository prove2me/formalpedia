-- Prove2me | Theorems.Thm_PerishablePricing_Backlog_theorem_1_concavity
-- name    : PerishablePricing.Backlog.theorem_1_concavity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:26:19.30108+00:00
-- url     : https://prove2.me/theorems/88b4e1e0-b23e-4361-92b6-96a773e45fda
-- title:
--   Theorem 1, p. 291, first sentence — fₜ, gₜ and φₜ are L♮-concave
-- statement:
--   In the backlogging model with the standing assumptions of §3 and §4, for $t = 1, \dots, T + 1$ and every noise value $\varepsilon$:
--
--   1. $f_t(s)$ is L♮-concave in $s$ on $\mathcal{S} = \mathcal{V}_{l-1,l-1}$;
--   2. $g_t(s, s_l, d \mid \varepsilon)$ is L♮-concave in $(s, s_l, d)$ on $\mathcal{V}_{l+1,l}$;
--   3. $\phi_t(s, s_l, d, a \mid \varepsilon)$ is L♮-concave in $(s, s_l, d, a)$ on $\mathcal{V}_{l+2,l}$.
--
--   Here $\mathcal{V}_{l+1,l}$ and $\mathcal{V}_{l+2,l}$ require $s_1 \le \dots \le s_{l-1} \le s_l$ and leave $d$ and $a$ unconstrained. This is the structural half of Theorem 1, the output of the induction over the dynamic program; the monotonicity of the optimal policy follows from it.
--
--   **Formalization Note** Time is counted in periods to go: part 1 holds for every `f n`, $n \ge 0$ (which covers $t = T+1$, where $f_{T+1} = 0$), while parts 2–3 are stated for `gN n` and `phiN n` with continuation `f n` (periods $t \le T$; $g_{T+1}$ and $\phi_{T+1}$ are not defined on the page). The joint vectors are 0-based in `Fin (L+2)` and `Fin (L+3)`. The §4 assumption is the hypothesis $(1 - \gamma)c \le h^-$.
-- source:
--   Chen, Pang, Pan, Coordinating Inventory Control and Pricing Strategies for Perishable Products, Oper. Res. 62(2), 2014, Theorem 1, first sentence, p. 291 (PDF p. 9)

import Mathlib
import Definitions.Def_PerishablePricing_Backlog_Model

namespace PerishablePricing.Backlog

/-- Theorem 1 (p. 291), first sentence: for every number of periods to go, `f_t(s)` is
L♮-concave on `𝒮 = 𝒱_{l−1,l−1}`, and for every noise value `ε`, `g_t(s, s_l, d | ε)` is
L♮-concave on `𝒱_{l+1,l}` (coordinates `(s, s_l, d)`) and `φ_t(s, s_l, d, a | ε)` is L♮-concave on
`𝒱_{l+2,l}` (coordinates `(s, s_l, d, a)`); `d` and `a` are unconstrained reals. -/
theorem theorem_1_concavity {L k : ℕ} (M : Model L k) (hc : (1 - M.γ) * M.c ≤ M.hm) :
    (∀ n : ℕ, LNatConcaveOn (V L L) (M.f n)) ∧
      (∀ (n : ℕ) (ε : ℝ), LNatConcaveOn (V (L + 2) (L + 1)) (M.gJoint n ε)) ∧
      (∀ (n : ℕ) (ε : ℝ), LNatConcaveOn (V (L + 3) (L + 1)) (M.phiJoint n ε)) := by sorry

end PerishablePricing.Backlog
