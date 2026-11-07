-- Prove2me | Theorems.Thm_PrivLittlestone_lemma_5_2
-- name    : PrivLittlestone.lemma_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:30:37.642195+00:00
-- url     : https://prove2.me/theorems/26b3079a-3105-4e7a-aa8f-d62180c7ec5c
-- title:
--   Lemma 5.2 — sampled majority on an oblivious sequence: every mistake has $Q_S$-error $\ge 1/3$ except with probability $\beta/(4K)$
-- statement:
--   Let $Q$ be the phase's starting distribution (any finitely supported distribution on classifiers) and let $z = ((x_t, y_t))_{t=1}^T$ be a fixed input sequence, $T \ge 1$. Let $K \ge 1$, $0 < \beta \le 1/2$, and let $m$ be odd with
--   $$
--   m \ge 18 \log\frac{8K(T+1)}{\beta},
--   $$
--   as in (11) with $c_{\mathrm{maj}} = 18$. Then, except with probability $\beta/(4K)$ over independent draws $h_1, \dots, h_m \sim Q$, every mistake of the sampled majority on the fixed sequence has $Q$-error at least $1/3$:
--   $$
--   \mathrm{Maj}(h_1, \dots, h_m)(x_t) \neq y_t \ \Longrightarrow\ Q[h(x_t) \neq y_t] \ge \tfrac13 \quad \text{for every } t .
--   $$
--
--   This proves condition (A2) for majority aggregation on oblivious streams.
--
--   Differences from the source:
--
--   - generalization: Q_S, the phase's starting distribution, and m = oddceil(c_maj log(8K(T+1)/β)) with K = ⌈c_ph dΛ⌉ → any finitely supported distribution Q, any K ≥ 1 and any odd m ≥ 18 log(8K(T+1)/β); reason: (11)'s m is odd and at least 18 log(8K(T+1)/β), and Q_S is finitely supported
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), Lemma 5.2, p.10, with (11), p.10, and c_maj = 18, Appendix C.1, p.24

import Mathlib
import Definitions.Def_PrivLittlestone_majority
import Definitions.Def_PrivLittlestone_prodProb

namespace PrivLittlestone

/-- **Lemma 5.2 (Majority on an oblivious sequence)** (He–He, *Private Online Learning of
Littlestone Classes and Matroid Flats*, STOC 2027 submission manuscript (sha256
21480556…c562), Lemma 5.2, p.10, with `m` as in (11) and `c_maj = 18` from Appendix C.1, p.24).
Let `Q` be a finitely supported distribution on classifiers (the phase's starting distribution
`Q_S`) and `z = ((x_t, y_t))_{t ≤ T}` a fixed input sequence. If `m` is odd and
`m ≥ 18 log(8K(T + 1)/β)`, then, except with probability `β/(4K)` over `m` independent draws
`h_1, …, h_m ∼ Q`, every mistake of the sampled majority `Maj(h_1, …, h_m)` on `z` has `Q`-error at
least `1/3`: `Q[h(x_t) ≠ y_t] ≥ 1/3` whenever `Maj(h_1, …, h_m)(x_t) ≠ y_t`. -/
theorem lemma_5_2 {X : Type*} {T : ℕ} (z : Fin T → X × Bool) (supp : Finset (X → Bool))
    (q : (X → Bool) → ℝ) (hq0 : ∀ f ∈ supp, 0 ≤ q f) (hq1 : ∑ f ∈ supp, q f = 1)
    (K m : ℕ) (β : ℝ) (hK : 1 ≤ K) (hT : 1 ≤ T) (hβ : 0 < β) (hβ1 : β ≤ 1 / 2) (hm : Odd m)
    (hm18 : 18 * Real.log (8 * (K : ℝ) * ((T : ℝ) + 1) / β) ≤ (m : ℝ)) :
    1 - β / (4 * (K : ℝ)) ≤
      prodProb supp q m (fun h => ∀ t : Fin T, majority h (z t).1 ≠ (z t).2 →
        (1 : ℝ) / 3 ≤ ∑ f ∈ supp, q f * (if f (z t).1 ≠ (z t).2 then 1 else 0)) := by sorry

end PrivLittlestone
