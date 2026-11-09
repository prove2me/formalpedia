-- Prove2me | Theorems.Thm_RecoveryStorage3SUM_Adaptive_lemma_4_8
-- name    : RecoveryStorage3SUM.Adaptive.lemma_4_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:08:36.512501+00:00
-- url     : https://prove2.me/theorems/453ab693-334b-48f4-992b-f1644aaf6a79
-- title:
--   Lemma 4.8 — the uncapped expansion reads at most $L$ entries
-- statement:
--   Fix a run with prime $p$ that is clean for $c$, and let $r=c\bmod p$ with $|M_r|\le 2n^\delta\log^2 n$. For arbitrary inverter answers, the full expansion, before any cap, lists at most
--   $$L=\lceil 6n^\delta\log^2 n\rceil$$
--   entries.
--
--   Hence the reading cap never stops the expansion in such a run, so the cap gives a worst-case time bound without losing pairs.
--
--   Differences from the source:
--   - generalization: $\delta\in[0,1)$ and the source run with its bounded equal-size inputs, sampled R and FN answers → any real $\delta$, arbitrary finite integer sets A, B and R, arbitrary K, partitions and inverter answers, any positive modulus p and any integer target c, retaining cleanliness and the small-class bound; reason: the full-expansion counting bound uses only verification, cleanliness and the class-size bound; every source run is included
--   - encoding: "the expansion reads at most $L$ entries" → the length of the expansion with no cap applied; reason: a statement about the capped loop would be a tautology
-- source:
--   Amir Carmel, Yakov Kosoburd, Robert Krauthgamer, STOC 2027 submission #561 (October 2026), Lemma 4.8, p.12

import Mathlib
import Definitions.Def_RecoveryStorage3SUM_Adaptive_Construction

set_option autoImplicit false

namespace RecoveryStorage3SUM.Adaptive

/-- Lemma 4.8, p.12: in a run clean for `c` with `|M_r| ≤ 2 n^δ log² n`, `r = c mod p`, the **uncapped**
expansion has at most `L` entries, whatever the inverters answer. -/
theorem lemma_4_8 (δ : ℝ) {A : Finset ℤ} {K : ℕ} (B R : Finset ℤ)
    (run : Attempt A K (numParts A.card δ)) (inv : Fin K → Fin (numParts A.card δ) → ℕ → Option ℕ)
    (c : ℤ) (hp : 0 < run.p) (hclean : CleanFor B R run.p c)
    (hM : ((unmarkedClass A B R run.p (residue run.p c)).card : ℝ) ≤ 2 * heavyThreshold A.card δ) :
    (expansion B R run inv (residue run.p c)).length ≤ numParts A.card δ := by sorry

end RecoveryStorage3SUM.Adaptive
