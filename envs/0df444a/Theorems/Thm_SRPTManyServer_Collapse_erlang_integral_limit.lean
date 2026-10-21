-- Prove2me | Theorems.Thm_SRPTManyServer_Collapse_erlang_integral_limit
-- name    : SRPTManyServer.Collapse.erlang_integral_limit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:03:45.449859+00:00
-- url     : https://prove2.me/theorems/01fd822e-d548-4a21-9db3-a12aa647ab18
-- title:
--   Proof of Lemma 4, p. 17 — $\bigl(\int_0^\infty (1+t/s)^{s} e^{-t}\,dt\bigr)^{-1} \to 0$ as $s \to \infty$
-- statement:
--   As the number of servers $s \to \infty$,
--   $$\left(\int_0^\infty \Bigl(1 + \frac ts\Bigr)^{s} e^{-t}\,dt\right)^{-1} \longrightarrow 0,$$
--   and equivalently the Erlang loss probability with offered load equal to the number of servers vanishes:
--   $$E(s, s) = \frac{s^s/s!}{\sum_{k=0}^{s} s^k/k!} \longrightarrow 0.$$
--
--   This is the limit used in the proof of Lemma 4: the blocking probability $\mathrm{Pb}^\lambda$ of the critically loaded class 1 loss queue tends to zero, so that $\mathrm{Th}^\lambda_{L,1}/\lambda \to G(\tau)$.
--
--   **Formalization Note** The index $s$ ranges over $\mathbb N$. At $s = 0$ the expressions are defined, with $t/0 = 0$ in Lean, and they do not affect the limit.
-- source:
--   Dong & Ibrahim, On the SRPT scheduling discipline in many-server queues with impatient customers, arXiv:2102.05789v1, p. 17, proof of Lemma 4 (final display)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Erlang

namespace SRPTManyServer.Collapse

open Filter Topology

/-- **The critically loaded Erlang limit** (proof of Lemma 4, p. 17). As the number of servers
`s → ∞`, `(∫_0^∞ (1 + t/s)^s e^{-t} dt)⁻¹ → 0`; equivalently the Erlang loss probability with offered
load equal to the number of servers, `E(s, s)`, tends to `0`. -/
theorem erlang_integral_limit :
    Tendsto (fun s : ℕ => (∫ t in Set.Ioi (0 : ℝ), (1 + t / (s : ℝ)) ^ s * Real.exp (-t))⁻¹)
      atTop (𝓝 0) ∧
    Tendsto (fun s : ℕ => KellyStochasticNetworks.erlang (s : ℝ) s) atTop (𝓝 0) := by sorry

end SRPTManyServer.Collapse
