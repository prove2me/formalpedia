-- Prove2me | Theorems.Thm_RSListDecodingCapacity_AllRates_lemma_3_11
-- name    : RSListDecodingCapacity.AllRates.lemma_3_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:09:47.531307+00:00
-- url     : https://prove2.me/theorems/356862ef-fca3-4475-ab02-77d00065823a
-- title:
--   Lemma 3.11 — lower bound (23) on $\dim\ker\Gamma$
-- statement:
--   Let $d\ge1$, $m$, $W$ be natural numbers, $\Gamma:V\to\mathbb F_q^I$ as in Section 3.2.2, and $h_r=\lceil(m-r)/d\rceil$. Then
--   $$\dim\ker\Gamma\ \ge\ \sum_{r=0}^{m-1}\max\Big(0,\ (r-h_r+1)(m-h_r+1)\,\Lambda(W+r)\Big). \tag{23}$$
--
--   Together with $\dim V$ and rank–nullity this bounds the rank of $\Gamma$ in Lemma 3.12.
--
--   Differences from the source:
--   - generalization: d, m, W the parameters of §3 → arbitrary natural numbers d ≥ 1, m, W; reason: V, Γ, h_r and Λ are defined from d, m, W alone; the §3 values are an instance
--   - generalization: q a sufficiently large prime (standing convention of §2, p.12) → every prime q; reason: the statement holds over every prime field and the source specializes it to large q; the argument uses no lower bound on q
--   - encoding: the integers r − h_r + 1 and m − h_r + 1 → integer (ℤ) arithmetic, h_r = ⌈(m − r)/d⌉ as an integer ceiling; reason: no natural-number truncation; max(0, ·) is taken in ℤ as in the source
-- source:
--   Joshua Brakensiek, Yeyuan Chen, Aaron Putterman, Zihan Zhang, Kai Zhe Zheng, Algorithmic List Decoding of Reed–Solomon Codes up to Capacity, STOC 2027 submission #565 (October 2026), p.22, Lemma 3.11, (23)

import Mathlib
import Definitions.Def_RSListDecodingCapacity_AllRates_Parameters
import Definitions.Def_RSListDecodingCapacity_AllRates_LocalRank

namespace RSListDecodingCapacity.AllRates

/-- **Lemma 3.11** (Brakensiek–Chen–Putterman–Zhang–Zheng, STOC 2027 submission #565, p.22), (23):
`dim ker Γ ≥ ∑_{r=0}^{m−1} max(0, (r − h_r + 1)(m − h_r + 1) Λ(W + r))`, with
`h_r = ⌈(m − r)/d⌉`. -/
theorem lemma_3_11 (q : ℕ) (hq : q.Prime) (d m W : ℕ) (hd : 1 ≤ d) :
    (∑ r ∈ Finset.range m,
        max 0 (((r : ℤ) - hr d m r + 1) * ((m : ℤ) - hr d m r + 1) *
          (Lambda d ((W + r : ℕ) : ℝ) : ℤ))) ≤
      (Module.finrank (ZMod q) (LinearMap.ker (Gamma (ZMod q) d m W)) : ℤ) := by sorry

end RSListDecodingCapacity.AllRates
