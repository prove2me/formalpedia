-- Prove2me | Theorems.Thm_QualityEncroach_Uniform_benchmark_given_u
-- name    : QualityEncroach.Uniform.benchmark_given_u
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:23:12.81271+00:00
-- url     : https://prove2.me/theorems/6dc4457a-c6d9-483e-b1a2-f09d8641cb89
-- title:
--   §3.2, p. 9, (1)–(2) — benchmark subgame given u: q^N_R, w^N(u) = ku²/2 + u/2, Π^N_M(u) = u(1−ku)²/8, Π^N_R(u) = u(1−ku)²/16
-- statement:
--   Fix a quality cost $k>0$ and a quality $u$ with $0<u<1/k$, and consider the benchmark supply chain without a direct channel (§3.2). Write $q^N_R(w,u)=\tfrac12-\tfrac{w}{2u}$ and $w^N(u)=\tfrac{ku^2}{2}+\tfrac u2$. Then:
--
--   1. for every wholesale price $w$ with $q^N_R(w,u)\ge0$, the order $q^N_R(w,u)$ is the retailer's unique profit-maximizing order among all $q_R\ge 0$, where his profit is $\Pi^N_R(q_R,w,u)=(u(1-q_R)-w)q_R$;
--   2. $w^N(u)$ is the unique maximizer over $w\in\mathbb R$ of the manufacturer's anticipated profit $(w-ku^2)\,q^N_R(w,u)$;
--   3. $q^N_R(w^N(u),u)=\tfrac14-\tfrac{ku}{4}$;
--   4. at $w^N(u)$ the two profits are
--   $$\Pi^N_M(u)=\frac{u(1-ku)^2}{8},\qquad \Pi^N_R(u)=\frac{u(1-ku)^2}{16}.$$
--
--   These are equations (1) and (2) of the paper, the first two steps of the backward induction in the benchmark.
--
--   **Formalization Note.** The bound $u<1/k$ is the paper's footnote 1 (p. 28): it makes $q^N_R(w^N(u),u)>0$.
-- source:
--   Ha, Long & Nasiry, Quality in Supply Chain Encroachment, authors' manuscript, SSRN 3970373, p. 9, §3.2, equations (1)–(2); footnote 1, p. 28

import Mathlib
import Definitions.Def_QualityEncroach_Uniform_Game

namespace QualityEncroach.Uniform

/-- §3.2, p. 9, (1)–(2): the benchmark subgame for a given quality `u` with `0 < u < 1/k`.
(a) Whenever `q^N_R(w, u) = 1/2 − w/(2u) ≥ 0`, it is the retailer's unique best order.
(b) `w^N(u) = ku²/2 + u/2` is the unique maximizer of `w ↦ (w − ku²) q^N_R(w, u)`.
(c) `q^N_R(w^N(u), u) = 1/4 − ku/4`.
(d) The two profits at `w^N(u)` are `Π^N_M(u) = u(1 − ku)²/8` and `Π^N_R(u) = u(1 − ku)²/16`. -/
theorem benchmark_given_u (k u : ℝ) (hk : 0 < k) (hu : 0 < u) (huk : u < 1 / k) :
    (∀ w : ℝ, 0 ≤ qRN w u → ∀ qR : ℝ, 0 ≤ qR → qR ≠ qRN w u →
        benchRetailerPayoff ⟨w, u, qR⟩ < benchRetailerPayoff ⟨w, u, qRN w u⟩) ∧
    (∀ w : ℝ, w ≠ wN k u →
        (w - k * u ^ 2) * qRN w u < (wN k u - k * u ^ 2) * qRN (wN k u) u) ∧
    qRN (wN k u) u = 1 / 4 - k * u / 4 ∧
    benchMfrPayoff k ⟨wN k u, u, qRN (wN k u) u⟩ = PiNM k u ∧
    benchRetailerPayoff ⟨wN k u, u, qRN (wN k u) u⟩ = PiNR k u := by sorry

end QualityEncroach.Uniform
