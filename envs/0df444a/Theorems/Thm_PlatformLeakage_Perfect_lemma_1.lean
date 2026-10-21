-- Prove2me | Theorems.Thm_PlatformLeakage_Perfect_lemma_1
-- name    : PlatformLeakage.Perfect.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:41:27.534268+00:00
-- url     : https://prove2.me/theorems/ad9a84f3-2c57-4bc6-949b-1d10bcbe83c9
-- title:
--   Lemma 1, p. 15 — the closed forms (16)–(17) are the unique equilibrium demand rates on and off the platform
-- statement:
--   Consider the on-demand platform model with the standing assumptions, a provider type $j$ and a fee $q\ge0$. For every number $C\ge0$ of $j$-type providers sharing an on-platform queue at fee $q$, a rate $\lambda$ satisfies the customers' equilibrium condition (5) for that queue if and only if
--   $$\lambda=\lambda^j_p(C,q)=\mu\,\frac{C(v^j-q)^+}{c\phi+C(v^j-q)^+}.$$
--   Likewise, a rate $\lambda$ satisfies (5) for an off-platform $j$-type provider charging $q$ if and only if
--   $$\lambda=\lambda^j_o(q)=\mu\,\frac{(v^j-q-R_o)^+}{c\phi+(v^j-q-R_o)^+}.$$
--
--   Customers join until their net utility equals the outside option's, so the demand each provider faces is determined by its own fee and, on the platform, by how many providers share it. All later fee and participation decisions rest on these demand rates.
--
--   **Formalization Note** Condition (5) is encoded with the stability requirement $0\le\lambda<\mu$ of p. 11 in the joining case. The off-platform clause "$n^j_o\ge1$" of (5) is not part of the encoding, since the off-platform demand is that of an existing provider.
-- source:
--   He, Savin, Goh & Teo, Off-Platform Threats in On-Demand Services, SSRN working paper 3550646 (PDF of 2021-03-25), p. 15 (PDF 15), Lemma 1, (5), (16)–(17)

import Mathlib
import Definitions.Def_PlatformLeakage_Perfect_Model

namespace PlatformLeakage.Perfect

/-- Lemma 1 (p. 15): for fees `q ≥ 0`, the closed forms (16) and (17) are the unique solutions of the
customers' equilibrium conditions (5), on the platform for every queue size `C` and off the platform. -/
theorem lemma_1 (P : Params) (hP : P.Std) (j : PType) :
    (∀ (C : ℕ) (q lam : ℝ), 0 ≤ q → (IsEqDemandP P j C q lam ↔ lam = demandP P j C q)) ∧
    (∀ q lam : ℝ, 0 ≤ q → (IsEqDemandO P j q lam ↔ lam = demandO P j q)) := by sorry

end PlatformLeakage.Perfect
