-- Prove2me | Theorems.Thm_ShiMatchmaking_Communication_lemma_D_3
-- name    : ShiMatchmaking.Communication.lemma_D_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T15:48:41.273354+00:00
-- url     : https://prove2.me/theorems/7c92e7e8-5acf-4537-87e1-42567d2b0e86
-- title:
--   Lemma D.3 — consequence of the rectangle property of communication protocols
-- statement:
--   Let $n\ge64$ and $d^J\in[1/\sqrt n,1/2]$, and put $d^I=1/(nd^J)$. Take any terminating deterministic matchmaking protocol for the independent binary market $M(n,d^I,d^J)$ and any customer-provider pair $(i,j)$. Let $\Pi$ be the concatenated sequence of all message bits. Write $\pi_{11},\pi_{10},\pi_{01},\pi_{00}$ for its distributions conditional on $(b_{ij},c_{ij})$ being $(.99,.01),(.99,1),(0,.01),(0,1)$, respectively. All four conditioning events have positive probability. With the full sum norm $\|p-q\|_1=\sum_z|p(z)-q(z)|$, the printed target is
--   $$\tfrac12\|\pi_{11}-\pi_{00}\|_1\le\|\pi_{10}-\pi_{00}\|_1+\|\pi_{01}-\pi_{00}\|_1.$$
--   This is the rectangle estimate invoked in the proof of Lemma D.2(b). No rectangle factorization or transcript decoder is assumed. The statement retains the source's literal message model; the coding defect and a counterexample with left side one and right side zero are recorded in the mission findings.
--
--   Differences from the source:
--   - encoding: two populations labeled [n] and binary real preferences → tagged copies of Fin n and two Boolean matrices with exact rational value maps; reason: relabeling and bijective flag encodings preserve every profile, private observation, and protocol
--   - encoding: the transcript Π is all communicated bits, while x^Π denotes the returned matching → Π is the concatenation of the terminal history and the outcome is obtained from the operational run; reason: Definition 3 observes message boundaries; (D.29) does not supply a decoder from concatenated bits, and assuming one would remove source instances
--   - encoding: probabilities, expectations, and information under the binary market → explicit product masses and finite sums over profiles and distinct transcript values; reason: the source sample space is finite; zero-mass profiles contribute zero and no probabilistic parameter is discretized
--   - encoding: maximum finite protocol length over possible inputs → termination required on every supported profile and a finite-set maximum bit count; reason: finite support makes these the same finite-cost protocol class; unsupported runs do not affect cost or probability
--   - generalization: the four laws arise during the proof for a successful protocol and a low-error pair → the estimate is stated for every terminating protocol and every pair in the same density regime; reason: the source proof explicitly asserts the rectangle property for any protocol; specializing to the successful protocol and low-error pair recovers the entire displayed claim
-- source:
--   Peng Shi (2023), Optimal Matchmaking Strategy in Two-Sided Marketplaces, Management Science, DOI 10.1287/mnsc.2022.4444, supplied published 65-page artifact; Lemma D.3, PDF/printed p. 43, (D.54), with conditional-law preamble pp. 42–43.

import Definitions.Def_ShiMatchmaking_Communication_Matchmaking

namespace ShiMatchmaking.Communication

theorem lemma_D_3 (n : ℕ) (hn : 64 ≤ n) (dJ : ℝ)
    (hdlo : 1 / Real.sqrt (n : ℝ) ≤ dJ) (hdhi : dJ ≤ 1 / 2)
    (P : MatchmakingProtocol n (1 / ((n : ℝ) * dJ)) dJ) (i j : Fin n) :
    (1 / 2 : ℝ) * rangeL1 P.transcript (P.pairLaw i j true true) (P.pairLaw i j false false) ≤
      rangeL1 P.transcript (P.pairLaw i j true false) (P.pairLaw i j false false) +
      rangeL1 P.transcript (P.pairLaw i j false true) (P.pairLaw i j false false) := by sorry

end ShiMatchmaking.Communication
