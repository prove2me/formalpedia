-- Prove2me | Theorems.Thm_SantaClausNSW_MaxMin_appendix_E_2
-- name    : SantaClausNSW.MaxMin.appendix_E_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:34:58.714459+00:00
-- url     : https://prove2.me/theorems/512689af-63b6-4d48-968d-fe805ae3f1d7
-- title:
--   Appendix E.2 — capped rejection sampling with fair bits adds at most δ to the failure probability
-- statement:
--   For a distribution whose probabilities have common denominator $Q$, rejection sampling draws $\lceil\log_2Q\rceil$ fair bits and repeats if the resulting integer is at least $Q$; the accepted integer is uniform on $\{0,\dots,Q-1\}$ and is mapped to an outcome by the prescribed probabilities, and each trial succeeds with probability at least $1/2$. For a procedure making at most $s\ge1$ sampling calls and any $0<\delta<1$, cap each call at $\lceil\log_2(s/\delta)\rceil$ trials and abort if none succeeds: the abort probability is at most $\delta$, the truncated and untruncated procedures can be coupled to agree unless an abort occurs, so truncation adds at most $\delta$ to the failure probability, and each call uses $O(1+\log(s/\delta))$ trials of polynomial cost.
--
--   In Lean: conditioned on acceptance, the capped rejection sampler is uniform on $\{0,\dots,Q-1\}$; one trial is rejected with probability at most $1/2$; and for every program whose runs halt within work $B$ after at most $s$ sampling calls, the capped run halts within $c(1+B)^d(1+T)$ work, aborts with probability at most $\delta$, and every output event has probability within $\delta$ of its exact value.
--
--   Differences from the source:
--   - encoding: a procedure making sampling calls; its truncated version → a program on the mission's RAM; runCapped executes each sampling call by capped rejection sampling with T = ⌈log₂(s/δ)⌉ trials of ⌈log₂ Q⌉ fair bits (Q the lcm of the denominators); reason: the paragraph's construction on the mission's machine
--   - encoding: 'can be coupled to agree unless an abort occurs, so truncation adds at most δ to the failure probability' → for every event E of the output, |Pr_capped[E] − Pr_exact[E]| ≤ δ, and Pr[abort] ≤ δ; reason: a coupling that agrees outside an event of probability ≤ δ is equivalent to total-variation distance ≤ δ; it implies the failure-probability claim
--   - encoding: O(1 + log(s/δ)) trials per call, each polynomial in the encoding of the distribution → every capped run halts within c·(1 + B)^d·(1 + T) work, c, d fixed before P, s, δ; reason: each call runs at most T trials, charged T·(1 + ⌈log₂ Q⌉) on top of reading the distribution
--   - encoding: 0 < δ < 1 → real δ; reason: the paragraph does not restrict δ to rationals
-- source:
--   Chen, Feng, Hu, Li, Zhang, Santa Claus and Weighted Nash Social Welfare with Subadditive Valuations, arXiv:2611.05229 (held version, sha256 98a235d3…), p. 67, Appendix E.2

import Mathlib
import Definitions.Def_SantaClausNSW_MaxMin_Machine

namespace SantaClausNSW.MaxMin

/-- **Appendix E.2** (p. 67). Capped rejection sampling with `⌈log₂ Q⌉` fair bits per trial:
the accepted integer is uniform on `{0, …, Q − 1}` (all its values are equally likely) and one
trial is rejected with probability at most `1/2`. Moreover there are constants `c, d` such that
for every program `P`, oracle `O`, input, `s ≥ 1` and `0 < δ < 1`, if every run of `P` (with
exact sampling) halts within work `B` after at most `s` sampling calls, then running every
sampling call by rejection sampling with fair bits capped at `T = ⌈log₂(s/δ)⌉` trials, every run
halts (or aborts) within `c (1 + B)^d (1 + T)` work, it aborts with probability at most `δ`, and
for every event `E` of the output the two procedures' probabilities differ by at most `δ`. -/
theorem appendix_E_2 :
    (∀ (Q T : ℕ), 1 ≤ Q → ∀ r r' : ℕ, r < Q → r' < Q →
      cappedReject Q (Nat.clog 2 Q) T (some r) = cappedReject Q (Nat.clog 2 Q) T (some r')) ∧
    (∀ Q : ℕ, 1 ≤ Q → cappedReject Q (Nat.clog 2 Q) 1 none ≤ 1 / 2) ∧
    ∃ c d : ℕ, ∀ (P : Program) (O : Oracle) (input : List ℚ) (B s : ℕ) (δ : ℝ),
      1 ≤ s → 0 < δ → δ < 1 →
      (∀ st ∈ (run P O (B + 1) (initState input)).support,
        st.halted = true ∧ st.work ≤ B ∧ st.samples ≤ s) →
      (∀ st ∈ (runCapped ⌈Real.logb 2 (s / δ)⌉₊ P O (B + 1) (initState input)).support,
        st.halted = true ∧ st.work ≤ c * (1 + B) ^ d * (1 + ⌈Real.logb 2 (s / δ)⌉₊)) ∧
      probOf (runCapped ⌈Real.logb 2 (s / δ)⌉₊ P O (B + 1) (initState input))
        (fun st => st.aborted = true) ≤ δ ∧
      ∀ E : List ℚ → Prop,
        |probOf (runCapped ⌈Real.logb 2 (s / δ)⌉₊ P O (B + 1) (initState input))
            (fun st => E (outList st.mem)) -
          probOf (run P O (B + 1) (initState input)) (fun st => E (outList st.mem))| ≤ δ := by sorry

end SantaClausNSW.MaxMin
