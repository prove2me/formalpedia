-- Prove2me | Theorems.Thm_TailOptCaching_ETLRU_value_etlru_eq_optValue
-- name    : TailOptCaching.ETLRU.value_etlru_eq_optValue
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:23:29.254545+00:00
-- url     : https://prove2.me/theorems/18e94d19-3fdd-413f-bc5a-9b7b059d955c
-- title:
--   App. B, pp. 17–19 — ET-LRU attains the finite-horizon Bellman optimum from every well-formed belief state
-- statement:
--   Let $\sigma$ be any ET-LRU policy (Definition 1, any tie-break). For every horizon $M$, every starting stage $k$ and every well-formed post-decision state $z$, the expected total TEL of the next $M$ arrivals under $\sigma$ equals the finite-horizon value-to-go function of App. B:
--   $$V^\sigma_M(z) = V^\star_M(z).$$
--
--   This is the induction of the proof of Theorem 2: at the last arrival every policy is optimal, and if ET-LRU is optimal from arrival $k + 1$ on, choosing the myopic minimizer of (8) at arrival $k$ loses nothing.
--
--   **Formalization Note.** The state is required to be well formed (in particular $0 < \lambda_i \le \bar\lambda_i$); every state the model reaches is, and planning computations found the claim false from unreachable states with $\lambda_i > \bar\lambda_i$.
-- source:
--   Zhang, Li, Moallemi & Peng, Tail-Optimized Caching for LLM Inference, arXiv:2510.15152v1, pp. 17–19, App. B (proof of Theorem 2)

import Mathlib
import Definitions.Def_TailOptCaching_ETLRU_Model

open scoped ENNReal

namespace TailOptCaching.ETLRU

theorem value_etlru_eq_optValue (P : Params) (σ : Policy) (hσ : IsETLRU P σ) (M k : ℕ)
    (z : State) (hz : WellFormed P z) :
    value P σ M k z = optValue P M z := by sorry

end TailOptCaching.ETLRU
