-- Prove2me | Theorems.Thm_SecSampling_lemma_9
-- name    : SecSampling.lemma_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:32:00.438094+00:00
-- url     : https://prove2.me/theorems/cd70fedc-8923-4897-9361-a2bb5b6bdff9
-- title:
--   Lemma 9 — children and parent of a node (corrected: a parent exists only with at least two zeros)
-- statement:
--   Let $I$ be an instance of size $n$.
--
--   1. If $I$ contains a $0$, the instances of size $n+1$ in conflict with $I$ are exactly those obtained by inserting a new $0$ anywhere after the last $0$ of $I$.
--   2. If $I$ contains at least two $0$s, then $I$ is in conflict with exactly one instance of size $n-1$, namely the one obtained by removing the last $0$ of $I$.
--   3. If $I$ contains at most one $0$, then $I$ is in conflict with no instance of size $n-1$.
--
--   So every node with at least two zeros has a unique **parent**, and the nodes without a parent are exactly those with at most one zero.
--
--   Differences from the source:
--   - correction: I is in conflict with only one instance of size n − 1: the one where the last zero has been removed → for I with at least two 0s; and an I with at most one 0 is in conflict with no instance of size n − 1; reason: conflict requires both instances to contain a 0 (p.15): for I = 01, removing the last 0 gives 1, which has no 0, so I has no conflicting instance of size 1
--   - reading: the instances of size n+1 in conflict with I are those obtained by inserting a new zero after the last 0 of I → stated for I containing a 0; reason: "after the last 0 of I" is undefined otherwise, and an I without a 0 is in conflict with nothing
-- source:
--   J. Correa, A. Cristi, L. Feuilloley, T. Oosterwijk & A. Tsigonias-Dimitriadis, The Secretary Problem with Independent Sampling, arXiv:2011.07869v1, https://arxiv.org/abs/2011.07869v1, Lemma 9, p.16 (PDF p.17); proof of Lemma 19, p.24 ("nodes without a parent are exactly the nodes that have at most one 0")

import Mathlib
import Definitions.Def_SecSampling_ConflictGraph

namespace SecSampling

/-- **Lemma 9** (arXiv:2011.07869v1, p.16), corrected. Let `I` be an instance of size `n`.

1. If `I` contains a `0`, the instances of size `n + 1` in conflict with `I` are exactly those
   obtained by inserting a new `0` anywhere after the last `0` of `I`.
2. If `I` contains at least two `0`s, `I` is in conflict with exactly one instance of size `n − 1`:
   the one where the last zero of `I` has been removed.
3. If `I` contains at most one `0`, it is in conflict with no instance of size `n − 1`.

**Formalization Note.** Inserting at 0-based index `i` places the new `0` after the first `i`
bits; "after the last 0" is `lastZero I ≤ i ≤ n`. Removing the last zero is erasing 0-based
index `lastZero I − 1`. -/
theorem lemma_9 (I : List Bool) :
    (false ∈ I → ∀ J : List Bool, J.length = I.length + 1 →
      (Conflict I J ↔ ∃ i : ℕ, lastZero I ≤ i ∧ i ≤ I.length ∧ J = I.insertIdx i false)) ∧
    (2 ≤ I.count false → ∀ J : List Bool, J.length + 1 = I.length →
      (Conflict J I ↔ J = I.eraseIdx (lastZero I - 1))) ∧
    (I.count false ≤ 1 → ∀ J : List Bool, J.length + 1 = I.length → ¬ Conflict J I) := by sorry

end SecSampling
