-- Prove2me | Theorems.Thm_ShiMatchmaking_Communication_lemma_D_2
-- name    : ShiMatchmaking.Communication.lemma_D_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T15:48:34.543981+00:00
-- url     : https://prove2.me/theorems/bd23d980-9632-4580-86a7-9881eebf79fd
-- title:
--   Lemma D.2 — lower bound on mutual information (both clauses)
-- statement:
--   Let $n\ge64$, $0<\epsilon<.49$, and let $d^I,d^J\in[0,1]$ satisfy $d^Id^J=1/n$. Consider a deterministic matchmaking protocol terminating on the support of $M(n,d^I,d^J)$ and returning an $\epsilon$-stable outcome with probability at least $.99$. For a fixed pair $(i,j)$, let $G_{ij}$ indicate that it is good and $P_{ij}$ indicate that it is perfect, and let $x_{ij}$ be its matching indicator in the actual output. Suppose the pair is low-error:
--   $$\mathbb E[P_{ij}(1-x_{ij})+(1-G_{ij})x_{ij}]\le .04/n.$$
--   For the concatenated bit transcript $\Pi$, both printed bounds are asserted:
--   1. If $d^J=1$ and $d^I=1/n$, then $I(b_{ij},c_{ij};\Pi)>.05\log_2(n)/n$.
--   2. If $d^J\in[1/\sqrt n,1/2]$ and $d^I=1/(nd^J)$, then $I(b_{ij},c_{ij};\Pi)>.0004/(nd^J)$.
--
--   Mutual information is in bits. The low-error condition is unconditional, and no cardinality bound on the low-error set is assumed. These are the two information estimates used for Proposition 12(a,b). The literal-model counterexample in the findings is retained rather than excluded by an additional coding condition.
--
--   Differences from the source:
--   - encoding: two populations labeled [n] and binary real preferences → tagged copies of Fin n and two Boolean matrices with exact rational value maps; reason: relabeling and bijective flag encodings preserve every profile, private observation, and protocol
--   - encoding: the transcript Π is all communicated bits, while x^Π denotes the returned matching → Π is the concatenation of the terminal history and the outcome is obtained from the operational run; reason: Definition 3 observes message boundaries; (D.29) does not supply a decoder from concatenated bits, and assuming one would remove source instances
--   - encoding: probabilities, expectations, and information under the binary market → explicit product masses and finite sums over profiles and distinct transcript values; reason: the source sample space is finite; zero-mass profiles contribute zero and no probabilistic parameter is discretized
--   - encoding: maximum finite protocol length over possible inputs → termination required on every supported profile and a finite-set maximum bit count; reason: finite support makes these the same finite-cost protocol class; unsupported runs do not affect cost or probability
-- source:
--   Peng Shi (2023), Optimal Matchmaking Strategy in Two-Sided Marketplaces, Management Science, DOI 10.1287/mnsc.2022.4444, supplied published 65-page artifact; Lemma D.2, PDF/printed p. 41, (D.35)–(D.36); standing context and error variables pp. 40–41.

import Definitions.Def_ShiMatchmaking_Communication_Matchmaking

namespace ShiMatchmaking.Communication

theorem lemma_D_2 (n : ℕ) (hn : 64 ≤ n) (ε dI dJ : ℝ)
    (hεpos : 0 < ε) (hεhi : ε < 49 / 100)
    (hdI : dI ∈ Set.Icc 0 1) (hdJ : dJ ∈ Set.Icc 0 1)
    (hdprod : dI * dJ = 1 / (n : ℝ))
    (P : MatchmakingProtocol n dI dJ) (hsuccess : 99 / 100 ≤ P.success ε)
    (i j : Fin n) (hlow : P.LowError i j) :
    (dJ = 1 → dI = 1 / (n : ℝ) →
      (5 / 100 : ℝ) * Real.logb 2 (n : ℝ) / n < P.pairInformation i j) ∧
    (1 / Real.sqrt (n : ℝ) ≤ dJ → dJ ≤ 1 / 2 → dI = 1 / ((n : ℝ) * dJ) →
      (4 / 10000 : ℝ) / ((n : ℝ) * dJ) < P.pairInformation i j) := by sorry

end ShiMatchmaking.Communication
