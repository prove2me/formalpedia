-- Prove2me | Theorems.Thm_SmoothedMIS_lemma_4_9
-- name    : SmoothedMIS.lemma_4_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:50:58.675725+00:00
-- url     : https://prove2.me/theorems/03f4db81-1a4a-4781-accf-3e0710084e68
-- title:
--   Lemma 4.9 — the base-low graph is well behaved
-- statement:
--   Fix $c>0$, any constant $a\ge48(c+3)$, and $\beta=2a$. Assume $M>0$ and $z_H<n/\sqrt{B_0}$, and let $E_0$ be the event that
--   1. every base-low vertex has at most $2\lambda$ random neighbours in $L_0$ — in particular $F_0$ has maximum degree at most $B_0+2\lambda=B$;
--   2. $|X_0^+|\le n/4$.
--
--   Then $E_0$ depends only on the random edges inside $L_0$: two outcomes of the coins that agree on every pair with both ends in $L_0$ agree on $E_0$. Moreover there is $n_0$, depending only on $c$ and $a$, such that for all $n\ge n_0$ and every such base graph,
--   $$
--   \mathbb P[E_0^c]\le 2n^{-c-2}.
--   $$
--
--   In Case (2b) the analysis conditions on an outcome of $F_0$ in $E_0$; the independence clause is what allows this.
--
--   Differences from the source:
--   - encoding: E0 depends only on the random edges inside L0 → two smoothing-coin outcomes agreeing on all pairs inside L0 agree on E0; reason: this is what the dependence claim means
--   - encoding: in particular, F0 has maximum degree at most B0 + 2λ = B → (a) implies deg_{F0}(v) ≤ B for every vertex v, with F0 a graph on all n vertices whose vertices outside L0 are isolated; reason: isolated vertices have degree 0 and degrees inside L0 are unchanged
--   - reading: for all sufficiently large n → ∃ n0 depending only on c and a, before the base graph G; reason: the thresholds of the proof involve only n, c and a
--   - encoding: the probabilities over the random edges R and the marks of Step 1 → the analysis law: smoothing coins on all pairs with probability min(1, β ln n/n) and independent mark coins κ_uv on all pairs with probability θ (clamped to [0,1]); reason: p.25 states that the per-pair coins have the same distribution as the algorithm; coins on edges of G change nothing; the clamps are the identity for large n
-- source:
--   Dey, Dufoulon, Moses Jr., Pandurangan, Smoothed Analysis for Distributed MIS (manuscript, STOC 2027 submission, sha256 dc2131db058466142db72a65b8482787f2b03f36c54eb18702fb92825cdfb42d), Lemma 4.9, p.24; proof pp.24–25 (PDF pp.26–27)

import Mathlib
import Definitions.Def_SmoothedMIS_testSet

open MeasureTheory

namespace SmoothedMIS

/-- **Lemma 4.9 (The base-low graph is well behaved)** (Dey, Dufoulon, Moses Jr., Pandurangan,
*Smoothed Analysis for Distributed MIS* (manuscript, sha256 dc2131db…), Lemma 4.9, p.24). Assume
`M > 0` and `z_H < n/√B0`. Let `E0` be the event that (a) every base-low vertex has at most `2λ`
random neighbors in `L0` — in particular, `F0` has maximum degree at most `B0 + 2λ = B` — and
(b) `|X0⁺| ≤ n/4`. Then `E0` depends only on the random edges inside `L0`, and, for all
sufficiently large `n`, `E0` fails with probability at most `2n^{−c−2}`.

**Formalization Note**
* Parameters as in §4.2 (p.20): `c > 0`, any `a ≥ 48(c + 3)`, `β = 2a`.
* "In particular": (a) implies `deg_{F0}(v) ≤ B` for every vertex (vertices outside `L0` are
  isolated in `F0`).
* "Depends only on the random edges inside `L0`": two coin outcomes that agree on every pair
  with both ends in `L0` agree on `E0`.
* The probability is over `anaLaw n (2a)`; `n0` depends on `c, a` only. -/
theorem lemma_4_9 : ∀ c : ℝ, 0 < c → ∀ a : ℝ, 48 * (c + 3) ≤ a →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)), 0 < M G → (zH G : ℝ) < n / Real.sqrt (B0 n) →
      (∀ ωR : Sym2 (Fin n) → Bool, EventE0a (2 * a) G ωR →
        ∀ v, (deg (F0 G ωR) v : ℝ) ≤ Bthr n (2 * a)) ∧
      (∀ ωR ωR' : Sym2 (Fin n) → Bool,
        (∀ u v, u ∈ L0 G → v ∈ L0 G → ωR s(u, v) = ωR' s(u, v)) →
        (EventE0 (2 * a) G ωR ↔ EventE0 (2 * a) G ωR'))) ∧
    ∃ n0 : ℕ, ∀ n ≥ n0, ∀ G : SimpleGraph (Fin n), 0 < M G →
      (zH G : ℝ) < n / Real.sqrt (B0 n) →
        (anaLaw n (2 * a) {ω | ¬ EventE0 (2 * a) G ω.1}).toReal ≤ 2 * (n : ℝ) ^ (-c - 2) := by sorry

end SmoothedMIS
