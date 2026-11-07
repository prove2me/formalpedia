-- Prove2me | Theorems.Thm_TimeSpaceMA_theorem_A_1
-- name    : TimeSpaceMA.theorem_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:57:17.858881+00:00
-- url     : https://prove2.me/theorems/9c8b1a20-92a6-465d-af2b-dea0e27f1ee9
-- title:
--   Theorem A.1 — dispersers [TUZ07, Theorem 2]
-- statement:
--   For all $n$, $k\le n$ and $\epsilon>0$, there is a bipartite graph with left side $[2^n]$, left degree $d=\mathrm{poly}(n)$ and right side $[R]$ with $R=\Omega(2^kd/n^3)$, such that every subset of at least $2^k$ left vertices has at least $(1-\epsilon)R$ distinct neighbors. The neighbors of a given left vertex can be listed in $\mathrm{poly}(n)$ time.
--
--   This is a result cited from the literature. It is the source of the sets in the isolation lemma below.
--
--   Differences from the source:
--   - encoding: poly(n), Ω(·), poly(n) time → n^e + e and c, chosen after ϵ and before n, k; d ≥ 1; reason: the page fixes ϵ first and uses the asymptotic notation in n
--   - encoding: for all n → 1 ≤ n; reason: the bound 2^k d/n³ is undefined at n = 0
--   - encoding: "can be listed in poly(n) time" → one coin-free RAM program on start memory [n, k, v], outputting d in M[0] and the neighbors in M[1+i], work ≤ n^e + e; reason: the page names no machine; decision 3 of the plan
-- source:
--   Williams, Xi, Short Non-Interactive Proofs for Time-Space Computations, STOC 2027 submission (manuscript sha256 184c2f95…), Theorem A.1, p.32 (citing Ta-Shma, Umans, Zuckerman, Combinatorica 2007, Theorem 2)

import Definitions.Def_TimeSpaceMA_RAM

namespace TimeSpaceMA

/-- **Theorem A.1** (Dispersers [TUZ07, Theorem 2]; Williams, Xi, STOC 2027 submission, manuscript sha256
184c2f95…, p.32). For all `n`, `k ≤ n`, `ϵ > 0` there is a bipartite graph with left side `[2^n]`, left
degree `d = poly(n)`, right side `[R]` with `R = Ω(2^k d / n³)`, such that every set of at least `2^k`
left vertices has at least `(1 − ϵ)R` distinct neighbors, and the neighbors of a left vertex can be listed
in `poly(n)` time.

**Formalization Note** `poly` and `Ω` are `n^e + e` and `c`, chosen after `ϵ`, before `n`. Multi-edges are
allowed (`Γ` need not be injective in the edge index). The listing program is uniform in `(n, k, v)`, with
start memory `[n, k, v]` and output `M[0] = d`, `M[1+i] = Γ(v, i)`. -/
theorem theorem_A_1 (ϵ : ℝ) (hϵ : 0 < ϵ) :
    ∃ (c : ℝ) (e : ℕ) (P : Program), 0 < c ∧ P.CoinFree ∧
      ∀ n k : ℕ, 1 ≤ n → k ≤ n →
        ∃ (d R : ℕ) (Γ : Fin (2 ^ n) → Fin d → Fin R),
          1 ≤ d ∧ d ≤ n ^ e + e ∧
          c * (2 : ℝ) ^ k * (d : ℝ) / (n : ℝ) ^ 3 ≤ (R : ℝ) ∧
          (∀ D : Finset (Fin (2 ^ n)), 2 ^ k ≤ D.card →
            (1 - ϵ) * (R : ℝ) ≤
              ((D.biUnion fun v => Finset.univ.image (Γ v)).card : ℝ)) ∧
          ∀ v : Fin (2 ^ n),
            ∃ st, P.RunsTo zeroTape (memOf [n, k, v.val]) st ∧ st.work ≤ n ^ e + e ∧
              st.mem 0 = d ∧ ∀ i : Fin d, st.mem (1 + i.val) = (Γ v i).val := by sorry

end TimeSpaceMA
