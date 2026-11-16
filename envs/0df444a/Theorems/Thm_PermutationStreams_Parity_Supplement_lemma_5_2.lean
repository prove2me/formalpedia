-- Prove2me | Theorems.Thm_PermutationStreams_Parity_Supplement_lemma_5_2
-- name    : PermutationStreams.Parity.Supplement.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:55:27.584342+00:00
-- url     : https://prove2.me/theorems/c88eb400-8017-4c1e-add4-2a07a2640c56
-- title:
--   Lemma 5.2 — the 312 excess identity and 312-avoidance
-- statement:
--   Let $\pi\in S_n$, $M_i=\max\{\pi_1,\dots,\pi_i\}$, and $E_{312}(\pi)=\sum_{i=1}^nT(M_i-\pi_i)-W(\pi)$ with $T(d)=d(d+1)/2$. Then
--
--   $$
--   E_{312}(\pi)=\sum_{\substack{i<j\\ \pi_i<\pi_j<M_i}}(\pi_j-\pi_i).
--   $$
--
--   Consequently $E_{312}(\pi)\ge0$, and $E_{312}(\pi)=0$ if and only if $\pi$ avoids the pattern $312$.
--
--   Testing whether one integer statistic vanishes therefore decides 312-avoidance; together with Lemma 5.1 it gives the logarithmic-space detector for $312$.
--
--   Differences from the source:
--   - encoding: positions and values in [n] = {1,…,n}, π ∈ S_n → Equiv.Perm (Fin n), with position i and value π i read as i + 1 and π i + 1; reason: every formula is evaluated on the shifted 1-based values; same instances
-- source:
--   Mark Braverman, Or Zamir, STOC 2027 submission #74 (October 2026), Parity and Pattern Detection in Permutation Streams, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/74.pdf (SHA-256 3f0b683e25232855e98d1caa358e35f2670633688d8a799e4d01a207aa5600ea), §5.2 pp. 9–10, Lemma 5.2

import Definitions.Def_PermutationStreams_Parity_Supplement_Patterns
import Definitions.Def_PermutationStreams_Parity_Supplement_Statistics

namespace PermutationStreams.Parity.Supplement

open PatternRangeCounting1593.RangeCounting

/-- Braverman–Zamir, STOC 2027 submission #74, Lemma 5.2, p.10. For every permutation `π` of
`[n]`, `E312(π) = ∑_{i<j, π_i < π_j < M_i} (π_j − π_i)`; consequently `E312(π) ≥ 0`, with equality
if and only if `π` avoids `312`. -/
theorem lemma_5_2 (n : ℕ) (π : Equiv.Perm (Fin n)) :
    E312 π = ∑ q ∈ (Finset.univ : Finset (Fin n × Fin n)).filter
        (fun q => q.1 < q.2 ∧ val π q.1 < val π q.2 ∧ val π q.2 < prefMax π q.1),
        (val π q.2 - val π q.1) ∧
    0 ≤ E312 π ∧ (E312 π = 0 ↔ Avoids pat312 π) := by sorry

end PermutationStreams.Parity.Supplement
