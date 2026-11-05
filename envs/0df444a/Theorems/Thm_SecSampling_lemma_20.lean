-- Prove2me | Theorems.Thm_SecSampling_lemma_20
-- name    : SecSampling.lemma_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:32:44.581132+00:00
-- url     : https://prove2.me/theorems/ecbce8e9-55b4-4c0d-9361-586aef4c1bda
-- title:
--   Lemma 20 — local operators preserve validity and do not decrease the window average (corrected: operator 2 not below the window)
-- statement:
--   Let $p\in(0,1)$, let $q_s$ be a valid randomized algorithm in the conflict graph, and fix a window $[n,n+t]$.
--
--   1. If $v$ has size $s\in[n,n+t-1]$, degree $d\ge 1/(1-p)$ and $q_s(v)>0$, then setting $q_s(v)=0$ and increasing the selection probability of every child of $v$ by $q_s(v)$ yields a valid algorithm whose average performance in the window is at least that of $q_s$.
--   2. If $v$ has size $s\ge n$, degree $d\le 1/(1-p)$ and $q_s(v)+q_r(v)<1$, then increasing $q_s(v)$ by $\varepsilon=1-q_s(v)-q_r(v)$ and setting $q_s(v')=0$ for every descendant $v'$ of $v$ yields a valid algorithm whose average performance in the window is at least that of $q_s$.
--
--   These moves are the engine of Lemma 17: they push every valid algorithm towards the fill-in strategy without lowering its window average.
--
--   Differences from the source:
--   - correction: operator 2 applies to a node v of degree d ≤ 1/(1 − p) of any size → to v of size s ≥ n; reason: below the window operator 2 can lower the average: p = 1/2, window [2, 2], q_s = 1 on 00, 01, 10 (valid, average 3/4); operator 2 at v = 0 (size 1, degree 1) selects 0 and zeroes its child 00, average 1/2. Lemma 17's proof uses it only inside the window; above the window the operator changes nothing in the window, so sizes s > n + t stay allowed
--   - reading: then for every descendant v′, set q_s(v′) = 0 and q_r(v′) = 1 → q_s(v′) = 0 for every descendant; q_r is recomputed from q_s; reason: q_r is defined from q_s (p.25), and after the operator q_r(v′) ≥ q_s(v) + q_r(v) = 1 for every descendant
--   - encoding: a monotone path is a possibly infinite path (p.15) → validity is required on finite monotone paths; reason: the terms are nonnegative, so a sum over an infinite path is bounded by 1 iff all its finite partial sums are
-- source:
--   J. Correa, A. Cristi, L. Feuilloley, T. Oosterwijk & A. Tsigonias-Dimitriadis, The Secretary Problem with Independent Sampling, arXiv:2011.07869v1, https://arxiv.org/abs/2011.07869v1, Lemma 20, p.25 (PDF p.26); Lemma 16, p.21 (PDF p.22), its deterministic case

import Mathlib
import Definitions.Def_SecSampling_FractionalSelection

namespace SecSampling

/-- **Lemma 20** (arXiv:2011.07869v1, p.25), corrected. Consider a valid randomized algorithm
`qs` in the conflict graph and a window `[n, n + t]`. Applying either local operator yields a
valid algorithm whose average performance in the window is at least as good:

1. if `qs` selects a node `v` of degree `d ≥ 1/(1−p)` of size `s ∈ [n, n + t − 1]` with
   probability `qs(v) > 0`: set `qs(v) = 0` and increase the selection probability of its children
   by `qs(v)`;
2. if for a node `v` of degree `d ≤ 1/(1−p)` **of size `s ≥ n`** the algorithm has
   `qs(v) + q_r(v) < 1`: increase `qs(v)` by `ε = 1 − qs(v) − q_r(v)` and set `qs(v′) = 0` for
   every descendant `v′`.

The size restriction `s ≥ n` in 2 is the correction: applied below the window, operator 2 can
lower the window average (p = 1/2, window [2, 2], v = 0). Above the window it changes nothing in
the window, so no upper bound on `s` is needed. -/
theorem lemma_20 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (qs : List Bool → ℝ) (hqs : IsValidSel qs)
    (n t : ℕ) :
    (∀ v : List Bool, n ≤ v.length → v.length < n + t → 1 / (1 - p) ≤ (degree v : ℝ) →
      0 < qs v →
      IsValidSel (localOp1 qs v) ∧ windowAvg p qs n t ≤ windowAvg p (localOp1 qs v) n t) ∧
    (∀ v : List Bool, n ≤ v.length → (degree v : ℝ) ≤ 1 / (1 - p) →
      qs v + removedFrac qs v < 1 →
      IsValidSel (localOp2 qs v) ∧ windowAvg p qs n t ≤ windowAvg p (localOp2 qs v) n t) := by sorry

end SecSampling
