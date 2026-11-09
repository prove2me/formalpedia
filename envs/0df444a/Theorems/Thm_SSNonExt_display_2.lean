-- Prove2me | Theorems.Thm_SSNonExt_display_2
-- name    : SSNonExt.display_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:00:40.190241+00:00
-- url     : https://prove2.me/theorems/b995d518-6046-405a-b522-14ed82e226ea
-- title:
--   Display (2) — $Z_T=2B-|T|$, $B\le Z_T\le 2B$, $P_T$ flat with $H_\infty(P_T)\ge b$
-- statement:
--   Let $b\ge2$, $V=\mathbb F_{2^b}$, $B=2^b$. For every $T\subseteq V$, the support $\Omega_T=\{C_i:i\in T\}\cup\{L_i,R_i:i\notin T\}$ has
--
--   $$Z_T=|\Omega_T|=2B-|T|,\qquad B\le Z_T\le 2B,$$
--
--   and the source $P_T=U_{\Omega_T}$ is flat with min-entropy $H_\infty(P_T)\ge b$.
--
--   This gives item 2 of Theorem 1.1 on the three-branch key set.
--
--   Differences from the source:
--   - encoding: Z_T = 2B − |T| with integer subtraction → natural-number subtraction 2 · 2^b − |T|; reason: |T| ≤ 2^b, so the subtraction never truncates
--   - encoding: min-entropy −log max_x P(x), logarithms base two → −Real.logb 2 of the finite maximum of the real values; reason: the same quantity
-- source:
--   Aggarwal, Secret Sharing Despite Non-Extractable Randomness, arXiv:2610.20173 (version of 2026-11-03, sha256 438a7f71…), §3, display (2) and the following sentence, p.6 (PDF p.6)

import Mathlib
import Definitions.Def_SSNonExt_TV
import Definitions.Def_SSNonExt_sourceClass

namespace SSNonExt

/-- **Display (2) and the sentence after it.** "Z_T = |Ω_T| = 2B − |T|" and "Since B ≤ Z_T ≤ 2B, every
P_T is flat with min-entropy at least b."
D. Aggarwal, *Secret Sharing Despite Non-Extractable Randomness*, arXiv:2610.20173 (version of
2026-11-03, sha256 438a7f71…), §3, display (2) and the following sentence, p.6 (PDF p.6).

Standing hypothesis of §3: `b ≥ 2`; `B = 2^b`.

**Formalization Note.** The natural-number subtraction `2 * 2^b − |T|` never truncates, since
`|T| ≤ |V| = 2^b`. Min-entropy is in bits (`Real.logb 2`). -/
theorem display_2 (b : ℕ) (hb : 2 ≤ b) (T : Finset (V b)) :
    (Omega T).card = 2 * 2 ^ b - T.card ∧
      2 ^ b ≤ (Omega T).card ∧ (Omega T).card ≤ 2 * 2 ^ b ∧
      IsFlat (srcP T) ∧ (b : ℝ) ≤ minEntropy (srcP T) := by sorry

end SSNonExt
