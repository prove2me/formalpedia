-- Prove2me | Theorems.Thm_Schnir_mann_rank
-- name    : Schnir.mann_rank
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T10:13:58.535141+00:00
-- url     : https://prove2.me/theorems/f94f4b3a-560f-4743-9b7d-a03ef663b6c5
-- title:
--   Mann's theorem at rank $r$: $\sigma(\sum_i A_i)\ge\min(1,\sum_i\sigma(A_i))$
-- statement:
--   Mann's theorem at arbitrary rank (Dyson's 1945 form). Let $A_1, \dots, A_r \subseteq \mathbb{Z}_{\ge 0}$ each contain $0$, and let $\sigma$ be the Schnirelmann density. Then the iterated sumset $A_1 + \cdots + A_r = \{a_1 + \cdots + a_r : a_i \in A_i\}$ satisfies
--
--   $$
--   \sigma(A_1 + \cdots + A_r) \;\ge\; \min\Bigl(1,\ \textstyle\sum_{i=1}^{r} \sigma(A_i)\Bigr).
--   $$
--
--   Dyson's original 1945 theorem proved this rank-$r$ statement (and its generalization replacing $r$ summands by sums with repetitions); the rank-2 case is Mann's theorem, proved on this platform as `Schnir.mann`. The rank-$r$ form follows by induction on $r$, and it is the natural multi-set input for results that split a representation among several different summand sets.
--
--   **Formalization Note** The sumset is the pointwise sum $\sum_i A_i$ over `Fin r` (`open Pointwise`); $\sigma$ is Mathlib's `schnirelmannDensity` with classical decidability.
-- source:
--   F. J. Dyson, A theorem on the density of sums of integers, J. London Math. Soc. 20 (1945), 8–14; rank-r form as in M. B. Nathanson, Additive Number Theory, GTM 165, §7.4. Rank-2 case proved on this platform as Schnir.mann.

import Mathlib

namespace Schnir

open Pointwise Classical in
theorem mann_rank {r : ℕ} (As : Fin r → Set ℕ) (h0 : ∀ i, 0 ∈ As i) :
    min 1 (∑ i, schnirelmannDensity (As i)) ≤ schnirelmannDensity (∑ i, As i) := by
  sorry

end Schnir
