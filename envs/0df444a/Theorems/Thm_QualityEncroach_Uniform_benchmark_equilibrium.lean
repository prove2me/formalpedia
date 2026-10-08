-- Prove2me | Theorems.Thm_QualityEncroach_Uniform_benchmark_equilibrium
-- name    : QualityEncroach.Uniform.benchmark_equilibrium
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:23:10.184125+00:00
-- url     : https://prove2.me/theorems/a502cf21-20db-422e-8195-9008d81961af
-- title:
--   §3.2, p. 9 — the benchmark equilibrium: u^N = 1/(3k), w^N = 2/(9k), q^N_R = 1/6, Π^N_M = 1/(54k), Π^N_R = 1/(108k)
-- statement:
--   Let $k>0$. The benchmark game without a direct channel (§3.2) has a subgame perfect equilibrium, and in every subgame perfect equilibrium the manufacturer chooses
--   $$u^N=\frac1{3k},\qquad w^N=\frac{2}{9k},$$
--   the retailer orders $q^N_R=\tfrac16$, and the equilibrium profits are
--   $$\Pi^N_M=\frac1{54k},\qquad \Pi^N_R=\frac1{108k}.$$
--
--   These are the benchmark profits against which encroachment is measured in Proposition 1(iii).
--
--   **Formalization Note.** The existence clause shows that the constants $1/(54k)$ and $1/(108k)$ used in the statement of Proposition 1(iii) are the profits of an actual benchmark equilibrium.
-- source:
--   Ha, Long & Nasiry, Quality in Supply Chain Encroachment, authors' manuscript, SSRN 3970373, p. 9, §3.2, display after (2)

import Mathlib
import Definitions.Def_QualityEncroach_Uniform_Game

namespace QualityEncroach.Uniform

/-- §3.2, p. 9: the benchmark game has a subgame perfect equilibrium, and every one has
`u^N = 1/(3k)`, `w^N = 2/(9k)`, `q^N_R = 1/6`, `Π^N_M = 1/(54k)` and `Π^N_R = 1/(108k)`. -/
theorem benchmark_equilibrium (k : ℝ) (hk : 0 < k) :
    (∃ τ : BenchProfile, IsBenchSPE k τ) ∧
    ∀ τ : BenchProfile, IsBenchSPE k τ →
      τ.u = 1 / (3 * k) ∧ τ.w = 2 / (9 * k) ∧ τ.path.qR = 1 / 6 ∧
      benchMfrPayoff k τ.path = 1 / (54 * k) ∧
      benchRetailerPayoff τ.path = 1 / (108 * k) := by sorry

end QualityEncroach.Uniform
