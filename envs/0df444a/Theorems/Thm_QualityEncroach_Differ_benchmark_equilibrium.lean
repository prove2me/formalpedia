-- Prove2me | Theorems.Thm_QualityEncroach_Differ_benchmark_equilibrium
-- name    : QualityEncroach.Differ.benchmark_equilibrium
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:27:13.333465+00:00
-- url     : https://prove2.me/theorems/9104e024-9da1-4c8e-971a-14afc6fda1c4
-- title:
--   §3.2, p. 9 — benchmark equilibrium: u^N = 1/(3k), w^N = 2/(9k), q^N_R = 1/6, Π^N_M = 1/(54k), Π^N_R = 1/(108k)
-- statement:
--   Consider the benchmark game of §3.2 without a direct channel, with cost-of-quality parameter $k>0$: the manufacturer chooses a wholesale price $w$ and a quality $u>0$, and the retailer then orders $q_R\ge0$ at the market-clearing price $u(1-q_R)$.
--
--   Every subgame-perfect equilibrium has the manufacturer choosing
--
--   $$
--   u^N=\frac{1}{3k},\qquad w^N=\frac{2}{9k},
--   $$
--
--   the retailer ordering $q^N_R=\tfrac16$ on the path, and equilibrium profits
--
--   $$
--   \Pi^N_M=\frac{1}{54k},\qquad \Pi^N_R=\frac{1}{108k}.
--   $$
--
--   Moreover, a subgame-perfect equilibrium exists.
--
--   These are the benchmark profits to which Propositions 1(iii) and 4(ii) compare the profits under encroachment.
-- source:
--   Ha, Long & Nasiry, Quality in Supply Chain Encroachment, authors' manuscript, SSRN 3970373, p. 9, §3.2 (u^N, w^N, q^N_R, Π^N_M, Π^N_R)

import Mathlib
import Definitions.Def_QualityEncroach_Differ_Benchmark

namespace QualityEncroach.Differ

theorem benchmark_equilibrium (k : ℝ) (hk : 0 < k) :
    (∀ τ : BenchProfile, IsBenchSPE k τ →
      τ.u = 1 / (3 * k) ∧ τ.w = 2 / (9 * k) ∧ τ.path.qR = 1 / 6 ∧
      benchMfrPayoff k τ.path = 1 / (54 * k) ∧ benchRetailerPayoff τ.path = 1 / (108 * k)) ∧
    ∃ τ : BenchProfile, IsBenchSPE k τ := by sorry

end QualityEncroach.Differ
