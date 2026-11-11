-- Prove2me | Theorems.Thm_SAInterp_Res2_lemma_7_1
-- name    : SAInterp.Res2.lemma_7_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:42:00.231948+00:00
-- url     : https://prove2.me/theorems/01cc9b54-ba13-429d-9a1e-8eca37430f1c
-- title:
--   Lemma 7.1 — E_µ vanishes on every witnessing conjunction of block degree ≤ d
-- statement:
--   For all sufficiently large $n$, with $d=\lfloor n/100\rfloor$, the following holds. For every indicator conjunction $C$ of $\mathrm{CPLS}_n$ with $\mathrm{bdeg}(C)\le d$ that is witnessing, meaning $C\Rightarrow\bar C_i$ for some clause $C_i$ of $\mathrm{CPLS}_n$,
--   $$E_\mu[C]=0.$$
--   This is the nonwitnessing half of Theorem 6.2.
--
--   Differences from the source:
--   - reading: the standing assumption of §6 "Let n be sufficiently large" → ∃ N0, ∀ n ≥ N0; reason: explicit form of the standing assumption.
--   - reading: d = n/100 → d = ⌊n/100⌋; reason: µ needs an integer d.
-- source:
--   Acheampong, Davis, Robere, Polynomial Interpolation for Sherali-Adams Lower Bounds, STOC 2027 submission (manuscript sha256 8de0a787…), p. 33 (PDF p. 35), Lemma 7.1

import Mathlib
import Definitions.Def_SAInterp_Res2_Indicator
import Definitions.Def_SAInterp_Res2_CPLS
import Definitions.Def_SAInterp_Res2_CPLSDist

namespace SAInterp.Res2

/-- Lemma 7.1 (p. 33), for all sufficiently large `n`, with `d = ⌊n/100⌋`: `E_µ[C] = 0` for every
indicator conjunction `C` with `bdeg(C) ≤ d` that witnesses the falsity of a clause of
`CPLS_n`. -/
theorem lemma_7_1 :
    ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n → ∀ C : IndConj (cplsSize n),
      (∃ Ci ∈ CPLS n, IndWitnesses C Ci) → bdeg C ≤ cplsD n → Emu n (indConj C) = 0 := by sorry

end SAInterp.Res2
