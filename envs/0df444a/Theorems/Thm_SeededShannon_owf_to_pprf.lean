-- Prove2me | Theorems.Thm_SeededShannon_owf_to_pprf
-- name    : SeededShannon.owf_to_pprf
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:46:39.065973+00:00
-- url     : https://prove2.me/theorems/b857aea9-2d71-4465-938a-1c0bd0a19fee
-- title:
--   Proof of Theorem 6.13 — one-way functions give $t$-puncturable PRFs
-- statement:
--   If one-way functions exist, then for every polynomially bounded puncturing bound $t(\lambda)$ there is a $t$-puncturable pseudorandom function $\Pi_{\mathrm{PPRF}}$ in the sense of Definition 3.4: polynomial-time, functionality preserving, and selectively punctured pseudorandom against nonuniform polynomial-size adversaries.
--
--   The paper cites this result ([BW13, KPTZ13, BGI14]) in the proof of Theorem 6.13; it supplies the PRF of Construction 6.1 and the PRF inside the puncturable pseudorandom code of Theorem 4.13.
--
--   **Formalization Note** One-way functions are the published `NoisyOWMPC.OWFExists`.
--
--   Differences from the source:
--   - reading: one-way functions give puncturable PRFs (puncturing bound unspecified) → for every polynomially bounded t, a t-puncturable PRF; reason: the goal uses t = N/ℓ, a polynomially bounded bound; the cited constructions puncture at any polynomial-size set
--   - reading: efficient / polynomial-time adversaries → nonuniform polynomial-size deterministic circuit families (`Distinguisher`, `CircFamily`); schemes are uniform machines; reason: Def. 3.1 allows non-uniform adversaries and the reductions hard-wire keys, so one nonuniform class is used throughout; a randomized adversary is matched by its best coins
--   - encoding: functionality preservation with probability 1 over KeyGen and Puncture → for all coin strings; reason: the coins are finitely many and uniform, so probability 1 is every outcome
--   - encoding: a puncturing set S of size at most t → a strictly lexicographically increasing list of at most t strings of length ℓin; reason: Def. 3.4 lists S in lexicographic order; the list is the canonical representation of the set
-- source:
--   Dujmovic, Lu, Silbak, Wichs, Shannon Rate Seeded Codes from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 52f4b606…a769709), proof of Theorem 6.13, p.47 (PDF p.50); cited at Definition 3.4, p.17

import Mathlib
import Definitions.Def_NoisyOWMPC_OWFExists
import Definitions.Def_SeededShannon_PPRF

set_option autoImplicit false

namespace SeededShannon

open NoisyOWMPC

/-- **One-way functions give puncturable PRFs** (Dujmovic, Lu, Silbak, Wichs, STOC 2027 submission
(manuscript sha256 52f4b606…a769709), proof of Theorem 6.13, p.47; cited from [BW13, KPTZ13, BGI14]
at Definition 3.4, p.17): if one-way functions exist, then for every polynomially bounded puncturing
bound `t(λ)` there is a `t`-puncturable PRF in the sense of Definition 3.4.

**Formalization Note** One-way functions are the published `NoisyOWMPC.OWFExists`
(nonuniform inverters). -/
theorem owf_to_pprf (hOWF : OWFExists) (t : ℕ → ℕ) (ht : PolyBounded t) :
    ∃ F : PPRF, F.IsPPRF t := by sorry

end SeededShannon
