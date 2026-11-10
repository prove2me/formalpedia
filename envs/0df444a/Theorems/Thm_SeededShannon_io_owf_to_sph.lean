-- Prove2me | Theorems.Thm_SeededShannon_io_owf_to_sph
-- name    : SeededShannon.io_owf_to_sph
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:46:29.772204+00:00
-- url     : https://prove2.me/theorems/917c67c7-01c1-4488-a497-a665fb439b5c
-- title:
--   Proof of Theorem 6.13 — iO and one-way functions give a single point binding hash
-- statement:
--   If indistinguishability obfuscation for polynomial-size circuits and one-way functions exist, then there is a single point binding hash $\Pi_{\mathrm{SPH}}$ (Definition 3.9): polynomial-time, input hiding, statistically binding at the setup input for every $n\le 2^\lambda$, and succinct, with hash length $\ell_{hash}(\lambda)$ a fixed polynomial in $\lambda$ independent of the input length.
--
--   The paper cites this result ([GWZ22]) in the proof of Theorem 6.13; the hash binds the public seed of Construction 6.1 to the challenge message.
--
--   **Formalization Note** iO is the published `NoisyOWMPC.IOScheme.IsIO`, one-way functions `NoisyOWMPC.OWFExists`.
--
--   Differences from the source:
--   - encoding: iO security against samplers Samp outputting (C₀, C₁, st) that agree everywhere with probability 1 − negl (Def. 3.1) → NoisyOWMPC.IOScheme.IsIO: fixed polynomial-size sequences (C₀,λ, C₁,λ, z_λ) of always-equivalent circuits; reason: equivalent: a nonuniform sampler can output a fixed triple, and conversely the best equivalent triple in a sampler's support bounds its advantage up to the negligible non-equivalence probability
--   - reading: a family of polynomial-size circuits, the two circuits of a pair of unspecified sizes → the two circuits of a pair have equal size and equal output length; reason: with unequal sizes no obfuscator can exist (the size is visible), so the hypothesis would be vacuous; the paper pads its circuits to common size (p.38)
--   - encoding: an efficient obfuscator with functionality preservation → IsIO also carries a public polynomial bound `len` on the obfuscated description and output-length preservation; reason: both follow from polynomial running time and functionality preservation
--   - reading: efficient / polynomial-time adversaries → nonuniform polynomial-size deterministic circuit families (`Distinguisher`, `CircFamily`); schemes are uniform machines; reason: Def. 3.1 allows non-uniform adversaries and the reductions hard-wire keys, so one nonuniform class is used throughout; a randomized adversary is matched by its best coins
-- source:
--   Dujmovic, Lu, Silbak, Wichs, Shannon Rate Seeded Codes from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 52f4b606…a769709), proof of Theorem 6.13, p.47 (PDF p.50); citing [GWZ22]

import Mathlib
import Definitions.Def_NoisyOWMPC_IOScheme
import Definitions.Def_NoisyOWMPC_OWFExists
import Definitions.Def_SeededShannon_SPH

set_option autoImplicit false

namespace SeededShannon

open NoisyOWMPC

/-- **Single point binding hash from iO and one-way functions** (Dujmovic, Lu, Silbak, Wichs, STOC
2027 submission (manuscript sha256 52f4b606…a769709), proof of Theorem 6.13, p.47, citing [GWZ22]):
if indistinguishability obfuscation for polynomial-size circuits and one-way functions exist, there
is a single point binding hash (Definition 3.9) whose output length is a fixed polynomial in `λ`
independent of the input length.

**Formalization Note** iO is the published `NoisyOWMPC.IOScheme.IsIO`, one-way functions
`NoisyOWMPC.OWFExists`; succinctness is a clause of `SPH.IsSPH`. -/
theorem io_owf_to_sph (hiO : ∃ O : IOScheme, O.IsIO) (hOWF : OWFExists) :
    ∃ H : SPH, H.IsSPH := by sorry

end SeededShannon
