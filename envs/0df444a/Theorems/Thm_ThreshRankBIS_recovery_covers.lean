-- Prove2me | Theorems.Thm_ThreshRankBIS_recovery_covers
-- name    : ThreshRankBIS.recovery_covers
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:09:00.607174+00:00
-- url     : https://prove2.me/theorems/df046a9e-cd06-4520-ac9c-c1a09ee5e7c7
-- title:
--   Recovery from the approximate cuts lists every maximal independent set of size $\ge n-T+1$
-- statement:
--   Let $G$ be a simple $d$-regular bipartite graph with $|X|=|Y|=n$, $d\ge1$, let $0<\rho<1$, $\kappa=\lceil256/\rho\rceil$, and let $\mathcal C$ be a list of approximate cuts satisfying (7). Let $T\ge1$ be an integer cutoff. Then every maximal independent set $I$ with $|I|\ge n-T+1$ is a target of Lemma 7 for $D_0=C\triangle Y$ for some $C\in\mathcal C$, with $b=T-1$ and $R=\kappa T$:
--
--   $$
--   |I|\ge n-(T-1),\qquad |I\triangle(C\triangle Y)|\le\kappa T .
--   $$
--
--   Consequently, applying recovery to each $C\triangle Y$, $C\in\mathcal C$, with $b=T-1$ and $R=\kappa T$ lists every maximal independent set of size at least $n-T+1$. This is step 3 of the algorithm.
--
--   Differences from the source:
--   - encoding: a simple d-regular bipartite graph G = (X ∪ Y, E) with |X| = |Y| = n and d ≥ 1 → the graph HiddenPartition.bip E of a biadjacency matrix E : Fin n → Fin n → Bool with all row and column sums d (IsRegular E d), 1 ≤ d and 0 < n; reason: every such graph is exactly one such matrix after numbering each side by Fin n; such a graph has n ≥ d ≥ 1, and 0 < n only excludes the empty matrix, which is vacuously d-regular
--   - encoding: on the list's simultaneous success event → the hypothesis that 𝒞 satisfies (7); reason: (7) is the property of the list on that event that the sentence uses
--   - reading: applying recovery to each C △ Y with b = T − 1, R = κT lists every maximal independent set of size at least n − T + 1 → every maximal independent I with |I| ≥ n − T + 1 satisfies the target conditions of Lemma 7 for D₀ = C △ Y, b = T − 1, R = κT, for some C ∈ 𝒞; reason: Lemma 7 lists exactly its targets, so 'is listed by some run' is equivalent to 'is a target of some run'; the time and output bound (10) is a separate claim not posed here
-- source:
--   Carlson–Kolla, Efficient Algorithms for Approximately Counting Bipartite Independent Sets in Low Threshold Rank Graphs, STOC 2027 submission (manuscript sha256 9b315e04…), p.10, the paragraph before display (10)

import Mathlib
import Definitions.Def_ThreshRankBIS_SatisfiesEq7
import Definitions.Def_ThreshRankBIS_hardcoreZ
set_option autoImplicit false
open Finset

namespace ThreshRankBIS

/-- **Recovery from the approximate cuts**, p.10 (the sentence before display (10)). Let `𝒞`
satisfy (7) and let `T ≥ 1` be an integer cutoff. Every maximal independent set `I` with
`|I| ≥ n − T + 1` is a target of Lemma 7 for `D_0 = C △ Y` for some `C ∈ 𝒞`, with `b = T − 1`
and `R = κT`: `|I| ≥ n − (T − 1)` and `|I △ (C △ Y)| ≤ κT`. So applying recovery to every
`C △ Y` lists every maximal independent set of size at least `n − T + 1`.

Source: Carlson–Kolla, STOC 2027 submission (manuscript sha256 9b315e04…), p.10, the paragraph
"For an integer cutoff T ≥ 1, apply recovery to each C△Y …".

**Formalization Note.** "On the list's simultaneous success event" is the hypothesis that `𝒞`
satisfies (7). The time and output-size bound (10) is not part of this statement. -/
theorem recovery_covers {n d : ℕ} (E : Fin n → Fin n → Bool) (hreg : IsRegular E d)
    (hd : 1 ≤ d) (hn : 0 < n) (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (𝒞 : Finset (Finset (V n)))
    (h7 : SatisfiesEq7 ρ E 𝒞) (T : ℕ) (hT : 1 ≤ T) :
    ∀ I : Finset (V n), IsMaxIndep E I → (n : ℤ) - T + 1 ≤ #I →
      ∃ C ∈ 𝒞, (n : ℤ) - ((T - 1 : ℕ) : ℤ) ≤ #I ∧
        #(symmDiff I (symmDiff C (Ys n))) ≤ kappa ρ * T := by sorry

end ThreshRankBIS
