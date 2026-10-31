-- Prove2me | Theorems.Thm_ShiMatchmaking_Communication_proposition_12
-- name    : ShiMatchmaking.Communication.proposition_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T15:48:53.003081+00:00
-- url     : https://prove2.me/theorems/00bacf92-bfaf-4f30-b1ee-238f5e363cfe
-- title:
--   Proposition 12 — lower bounds in communication cost (all three clauses)
-- statement:
--   For $M(n,d^I,d^J)$, take $n$ customers and $n$ providers, with independent benefits $b_{ij}=.99$ with probability $d^I$ and zero otherwise, and independent costs $c_{ij}=.01$ with probability $d^J$ and one otherwise. Communication cost is the maximum number of bits communicated on a supported input, divided by the number $2n$ of agents.
--
--   The printed target asserts that there exist positive universal real constants $\kappa_1,\kappa_2,\kappa_3$, chosen before the size, tolerance, density, and protocol, such that for every integer $n\ge64$ and $0<\epsilon<.49$ all three clauses hold:
--   1. Every deterministic matchmaking protocol producing an $\epsilon$-stable outcome with probability at least $.99$ in $M(n,1/n,1)$ has per-agent cost at least $\kappa_1\log n$.
--   2. For every $d^J\in[1/\sqrt n,1/2]$, every such protocol in $M(n,1/(nd^J),d^J)$ has per-agent cost at least $\kappa_2/d^J$.
--   3. Every one-round matchmaking protocol producing an $\epsilon$-stable outcome with probability at least $.99$ in $M(n,.5,.5)$ has per-agent cost at least $\kappa_3\log n$.
--
--   All protocols terminate on supported inputs. They use arbitrary finite binary messages, including empty messages, and the controller observes complete message histories. Transaction prices range over all real numbers. Stability is individual rationality and $u_i+v_j+2\epsilon\ge b_{ij}-c_{ij}$ for every pair. The source's literal message model permits a counterexample to the unrestricted clauses, recorded in the mission findings; this target has not been repaired by restricting its protocol class.
--
--   Differences from the source:
--   - encoding: two populations labeled [n] and binary real preferences → tagged copies of Fin n and two Boolean matrices with exact rational value maps; reason: relabeling and bijective flag encodings preserve every profile, private observation, and protocol
--   - encoding: probabilities, expectations, and information under the binary market → explicit product masses and finite sums over profiles and distinct transcript values; reason: the source sample space is finite; zero-mass profiles contribute zero and no probabilistic parameter is discretized
--   - encoding: maximum finite protocol length over possible inputs → termination required on every supported profile and a finite-set maximum bit count; reason: finite support makes these the same finite-cost protocol class; unsupported runs do not affect cost or probability
--   - encoding: unbased log n in bounds with existential universal constants → natural logarithm of the real coercion of n; reason: changing a fixed logarithm base rescales the existential positive constants and preserves the entire claim
--   - reading: Definition 3 divides by the number of agents, while D.5 and D.6 call L/n the per-agent cost → the cost is L/(2n); reason: the theorem uses the explicit definition and the agent set has two disjoint populations of size n; the proof normalization typo is recorded separately in I2
-- source:
--   Peng Shi (2023), Optimal Matchmaking Strategy in Two-Sided Marketplaces, Management Science, DOI 10.1287/mnsc.2022.4444, supplied published 65-page artifact; Proposition 12, PDF/printed p. 26, (33)–(34); Definitions 3–5, pp. 23–25; tolerance convention §2.3, p. 9.

import Definitions.Def_ShiMatchmaking_Communication_Matchmaking

namespace ShiMatchmaking.Communication

theorem proposition_12 :
    ∃ κ₁ κ₂ κ₃ : ℝ, 0 < κ₁ ∧ 0 < κ₂ ∧ 0 < κ₃ ∧
    ∀ (n : ℕ), 64 ≤ n → ∀ ε : ℝ, 0 < ε → ε < 49 / 100 →
      (∀ P : MatchmakingProtocol n (1 / (n : ℝ)) 1,
        99 / 100 ≤ P.success ε → κ₁ * Real.log (n : ℝ) ≤ P.cost) ∧
      (∀ dJ : ℝ, 1 / Real.sqrt (n : ℝ) ≤ dJ → dJ ≤ 1 / 2 →
        ∀ P : MatchmakingProtocol n (1 / ((n : ℝ) * dJ)) dJ,
        99 / 100 ≤ P.success ε → κ₂ / dJ ≤ P.cost) ∧
      (∀ P : OneRoundProtocol n,
        99 / 100 ≤ oneRoundSuccess P (1 / 2) (1 / 2) ε →
        κ₃ * Real.log (n : ℝ) ≤ oneRoundCost P (1 / 2) (1 / 2)) := by sorry

end ShiMatchmaking.Communication
