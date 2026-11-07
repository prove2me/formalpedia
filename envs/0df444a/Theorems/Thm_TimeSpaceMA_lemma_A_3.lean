-- Prove2me | Theorems.Thm_TimeSpaceMA_lemma_A_3
-- name    : TimeSpaceMA.lemma_A_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:57:15.481374+00:00
-- url     : https://prove2.me/theorems/cd95637c-1122-49ba-8c5c-a90e91867b54
-- title:
--   Lemma A.3 — isolation
-- statement:
--   For every $n\ge 2$ there are an $h$ with $n\le h\le n\,\mathrm{polylog}(n)$ and sets $J_1,\dots,J_h\subseteq[n]$, repetitions and empty sets allowed, such that:
--
--   1. the distinct nonempty sets in the list have total size at most $n\,\mathrm{polylog}(n)$, and these sets with the map $i\mapsto J_i$ are computable in $n\,\mathrm{polylog}(n)$ time;
--   2. every nonempty $D\subseteq[n]$ satisfies
--   $$\Pr_{i\in[h]}\bigl[|J_i\cap D|=1\bigr]\ge\frac{1}{\mathrm{polylog}(n)}.$$
--
--   Differences from the source:
--   - encoding: polylog(n) → C(log₂ n + 2)^K with one C, K for all n; reason: the standard meaning, with +2 so that the bound is at least C
--   - encoding: computed in n polylog(n) time → one coin-free RAM program on [n], work bound as stated, final memory satisfying EncodesFamily; reason: the page names no machine or layout; the layout determines the list and the map
--   - encoding: total size of distinct nonempty sets → total size of distinct sets; reason: an empty set contributes 0
-- source:
--   Williams, Xi, Short Non-Interactive Proofs for Time-Space Computations, STOC 2027 submission (manuscript sha256 184c2f95…), Lemma A.3, p.33

import Definitions.Def_TimeSpaceMA_RAM
import Definitions.Def_TimeSpaceMA_EncodesFamily
import Definitions.Def_TimeSpaceMA_polylogBound

namespace TimeSpaceMA

/-- **Lemma A.3** (Isolation; Williams, Xi, STOC 2027 submission, manuscript sha256 184c2f95…, p.33). For
every `n ≥ 2` there is `h` with `n ≤ h ≤ n polylog(n)` and a list `J₁, …, J_h ⊆ [n]` such that (a) the
distinct nonempty sets have total size at most `n polylog(n)`, and these sets and the map `i ↦ J_i` are
computable in `n polylog(n)` time, and (b) every nonempty `D ⊆ [n]` has
`Pr_{i ∈ [h]}[|J_i ∩ D| = 1] ≥ 1/polylog(n)`.

**Formalization Note** `polylog` is one `polylogBound C K`. The program is one coin-free RAM program with
start memory `[n]` and the output layout `EncodesFamily`. An empty set adds `0` to `distinctSize`. -/
theorem lemma_A_3 :
    ∃ (C : ℝ) (K : ℕ) (P : Program), 0 < C ∧ P.CoinFree ∧
      ∀ n : ℕ, 2 ≤ n →
        ∃ (h : ℕ) (J : Fin h → Finset (Fin n)),
          (n : ℝ) ≤ h ∧ (h : ℝ) ≤ n * polylogBound C K n ∧
          (distinctSize J : ℝ) ≤ n * polylogBound C K n ∧
          (∃ st, P.RunsTo zeroTape (memOf [n]) st ∧
            (st.work : ℝ) ≤ n * polylogBound C K n ∧ EncodesFamily st.mem J) ∧
          ∀ D : Finset (Fin n), D.Nonempty →
            1 / polylogBound C K n ≤
              ((Finset.univ.filter fun i => (J i ∩ D).card = 1).card : ℝ) / h := by sorry

end TimeSpaceMA
