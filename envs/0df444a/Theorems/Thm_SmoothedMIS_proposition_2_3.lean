-- Prove2me | Theorems.Thm_SmoothedMIS_proposition_2_3
-- name    : SmoothedMIS.proposition_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:47:53.948196+00:00
-- url     : https://prove2.me/theorems/9ebb70bf-b444-431a-a83f-b86d19e6cc5d
-- title:
--   Proposition 2.3 — MIS in $O(\log\Delta)+\tilde O(\log^3\log n)$ LOCAL rounds (Theorem 7 of [19])
-- statement:
--   Fix a constant $c>0$ and an identifier range $\kappa$. There is a randomized LOCAL algorithm, knowing $n$ and $\Delta$, and constants $C,k,n_0$ such that for all $n\ge n_0$:
--   1. its round budget satisfies $T(n,\Delta)\le C\ln(\Delta+2)+C(\ln\ln n)^3(1+\ln\ln\ln n)^k$ for every $\Delta$;
--   2. on every graph $H$ with at most $n$ vertices and maximum degree at most $\Delta$, with distinct identifiers in $\{0,\dots,n^\kappa-1\}$, the set it computes is an MIS of $H$ with probability at least $1-n^{-c}$ over the nodes' random bits.
--
--   This is the result of Ghaffari, Halldórsson, Maus and Nolin that the paper uses as a black box: Step 3 of Algorithm 1 applies it to $\mathcal G[V_{rest}]$, whose maximum degree is at most $B$, so that it costs $O(\sqrt{\ln n})$ rounds.
--
--   **Formalization Note** The success event need not be measurable (the algorithm is an arbitrary function of the tapes), so the statement provides a measurable sub-event of probability at least $1-n^{-c}$.
--
--   Differences from the source:
--   - reading: with high probability → with probability ≥ 1 − n^{−c} for every constant c > 0, the algorithm and its constants depending on c; reason: footnote 10, p.5, and §2, p.9 define w.h.p. this way
--   - reading: for any n-vertex graph H with maximum degree ∆ there exists a randomized LOCAL algorithm → one algorithm, chosen before n, ∆ and H, that knows (n, ∆); its round budget is a function of (n, ∆) only; reason: this is how Step 3 of Algorithm 1 uses it ("run with ∆ = B") and how the cited result is stated
--   - encoding: O(log ∆) + Õ(log³ log n) rounds → C ln(∆ + 2) + C (ln ln n)³ (1 + ln ln ln n)^k for n ≥ n0; reason: Õ(f) = O(f · polylog f) with f = ln³ ln n and ln f = 3 ln ln ln n + ln 3; ln(∆ + 2) is within a constant of ln ∆ for ∆ ≥ 2 and absorbs ∆ ≤ 1
--   - generalization: an n-vertex graph H with maximum degree ∆ → any graph with at most n vertices and maximum degree at most ∆, n and ∆ known to the nodes; reason: contains the n-vertex graphs of maximum degree exactly ∆; Step 3 runs it on 𝒢[V_rest], which has at most n vertices and maximum degree at most B ("with ∆ = B")
--   - reading: distinct identifiers of O(log n) bits (§1.5) → injective identifiers < n^κ for a constant κ fixed before the algorithm; reason: O(log n) bits means values below n^κ for a constant κ
--   - reading: the port-numbered LOCAL model (§1.5) → broadcast with multiset reception, a private fair-coin tape per node (LocalAlg); reason: with unbounded messages carrying identifiers this simulates ports after one round, so the existence claim is at least as strong
--   - encoding: with probability at least 1 − n^{−c} → a measurable sub-event of the success event with probability ≥ 1 − n^{−c} (inner measure); reason: the algorithm is an arbitrary function of the tapes, so the success event need not be measurable; when it is, the two agree
-- source:
--   Dey, Dufoulon, Moses Jr., Pandurangan, Smoothed Analysis for Distributed MIS (manuscript, STOC 2027 submission, sha256 dc2131db058466142db72a65b8482787f2b03f36c54eb18702fb92825cdfb42d), Proposition 2.3 (Theorem 7 of [19]), p.10 (PDF p.12)

import Mathlib
import Definitions.Def_SmoothedMIS_IsMIS
import Definitions.Def_SmoothedMIS_LocalAlg

open MeasureTheory

namespace SmoothedMIS

/-- **Proposition 2.3** (Theorem 7 of [19], Ghaffari–Halldórsson–Maus–Nolin) (Dey, Dufoulon,
Moses Jr., Pandurangan, *Smoothed Analysis for Distributed MIS* (manuscript, sha256 dc2131db…),
Proposition 2.3, p.10). For any `n`-vertex graph `H` with maximum degree `∆`, there exists a
randomized LOCAL algorithm that computes an MIS with high probability in
`O(log ∆) + Õ(log³ log n)` rounds.

**Formalization Note**
* "w.h.p." is `≥ 1 − n^{−c}` for an arbitrary constant `c > 0` fixed in advance (footnote 10,
  p.5); identifiers are distinct and `< n^κ` ("O(log n) bits"); `A`, `C`, `k`, `n0` depend on
  `c, κ` only.
* Nodes know `(n, ∆)`; the round budget is a function of `(n, ∆)` only, bounded by
  `C ln(∆ + 2) + C (ln ln n)³ (1 + ln ln ln n)^k` (the `O(log ∆)` term as `C ln(∆+2)`, the
  `Õ(f) = O(f · polylog f)` term with `f = ln³ ln n`).
* The graph has at most `n` vertices (`n` known), which contains the `n`-vertex case.
* The success event need not be measurable (the algorithm is an arbitrary function of the
  tapes): the statement asserts a measurable subevent of probability `≥ 1 − n^{−c}`. -/
theorem proposition_2_3 :
    ∀ c : ℝ, 0 < c → ∀ κ : ℕ, ∃ A : LocalAlg (ℕ × ℕ) Unit Bool, ∃ C : ℝ, ∃ k n0 : ℕ,
      (∀ n ≥ n0, ∀ Δ : ℕ, (A.rounds (n, Δ) : ℝ) ≤ C * Real.log ((Δ : ℝ) + 2) +
        C * Real.log (Real.log n) ^ 3 * (1 + Real.log (Real.log (Real.log n))) ^ k) ∧
      ∀ n ≥ n0, ∀ Δ : ℕ, ∀ (V : Type) [Fintype V], Fintype.card V ≤ n →
        ∀ H : SimpleGraph V, (∀ v, deg H v ≤ Δ) →
        ∀ ids : V → ℕ, Function.Injective ids → (∀ v, ids v < n ^ κ) →
          ∃ E : Set (V → ℕ → Bool), MeasurableSet E ∧
            E ⊆ {τ | IsMIS H (A.outSet H (n, Δ) ids τ)} ∧
            1 - (n : ℝ) ^ (-c) ≤ (tapeLaw V E).toReal := by sorry

end SmoothedMIS
