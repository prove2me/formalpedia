-- Prove2me | Theorems.Thm_PooledTestingAdaptivity_Gap_lemma_4_5
-- name    : PooledTestingAdaptivity.Gap.lemma_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:28:36.924417+00:00
-- url     : https://prove2.me/theorems/65b712ea-10bf-4a22-a902-9716898106e6
-- title:
--   Lemma 4.5 — Subcube half-thinning
-- statement:
--   Let $\pi$ be any normalized finite policy, let $E\subseteq[n]$ be its free coordinates, let $a$ assign health bits outside $E$, and fix any focal person $i$. For $v\in\{0,1\}^E$, let $x_a(v)$ be its extension and let $\bar v=1-v$. With the actual clearance indicator $d_i$ and actual occurrence-thinning probability $h_i$,
--
--   $$\sum_{v\in\{0,1\}^E}d_i(x_a(v))\le2\sum_{v\in\{0,1\}^E}h_i(P_\pi(x_a(v)),x_a(\bar v)).$$
--
--   The focal coordinate may be fixed healthy, fixed infected or free. No restriction on $E$, prior probabilities or utilities is introduced. This is the full subcube comparison, retaining the case where the focal health bit is complemented.
--
--   Differences from the source:
--   - encoding: people indexed by [n] and finite pool-labelled binary policies → people indexed by Fin n, health in Bool, and the published QTree with unit-valued stop leaves; reason: reindexing and tree constructors represent exactly the same health profiles, histories and policies
--   - encoding: probability over independent fair coins for individual occurrences → uniform finite average over test-position/person bits, with unused bits outside each pool; reason: dummy bits cancel from the average; each real occurrence has its own independent fair bit
--   - encoding: v ranges over bits on E and a over bits on its complement → dependent subtype domains for free and fixed coordinates; reason: the extension uses a only outside E and complements precisely the coordinates of v
-- source:
--   Edwin Lock, Nicholas Lopez, Francisco Marmolejo-Cossío, Jose Roberto Tello Ayala, David Parkes, STOC 2027 submission #1397 (October 2026), Lemma 4.5, Eq. (15), printed p. 15, PDF p. 16; proof printed pp. 15–17, PDF pp. 16–18; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1397.pdf

import Mathlib
import Definitions.Def_PooledTestingAdaptivity_Gap_HalfThinning

namespace PooledTestingAdaptivity.Gap

/-- Lemma 4.5, printed p.15 / PDF p.16, Eq.(15).
The focal coordinate may be fixed healthy, fixed infected, or free. -/
theorem lemma_4_5 {n : ℕ} (π : Policy n) (hπ : Normalized π)
    (E : Finset (Fin n)) (a : {i : Fin n // i ∉ E} → Bool) (i : Fin n) :
    (∑ v : {j : Fin n // j ∈ E} → Bool,
      clearanceIndicator π i (extendProfile E a v)) ≤
      2 * ∑ v : {j : Fin n // j ∈ E} → Bool,
        thinningClearance (run π (extendProfile E a v))
          (extendProfile E a (fun j => !(v j))) i := by sorry

end PooledTestingAdaptivity.Gap
