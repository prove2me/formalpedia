-- Prove2me | Theorems.Thm_TargetedSamplers_lemma_4_16
-- name    : TargetedSamplers.lemma_4_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:10:59.293981+00:00
-- url     : https://prove2.me/theorems/a4ca6fe0-15fd-4f9b-a813-f662cfa43952
-- title:
--   Lemma 4.16 — two-sided to one-sided quantified derandomization (corrected: T(n) must allow writing the query)
-- statement:
--   Let $T,C,Q:\mathbb N\to\mathbb N$ be monotone and time-constructible with $Q(x)<2^{x/2}$ for all $x$, $C(n)$ even and $n+C(n)/2\le K_0(T(n)+1)$. Let $Q'(x)=Q(2x)$ and let $T'$ be any time-constructible function with $T'(n+C(n)/2)=T(n)$. Then every $\Pi\in\mathrm{prBPTC}_Q[T,C]$ satisfies
--   $$\Pi\in\mathrm{prRTC}_{Q'}[T,C/2]^{\mathrm{prcoRTC}_{Q'}[T',O(n)]}:$$
--   there are a promise problem $\Pi'\in\mathrm{prcoRTC}_{Q'}[T',C']$ with $C'(m)\le Km$ and an oracle algorithm $A$ that witnesses $\Pi\in\mathrm{prRTC}_{Q'}[T,C/2]$ for every oracle answering $\Pi'$. $A$ makes exactly one oracle query, of length $n+C(n)/2$.
--
--   This is the second step of the proof of Theorem 4.30: two-sided error reduces to one-sided error at essentially no time cost.
--
--   Differences from the source:
--   - encoding: C(n)/2 coins → C(n) even; reason: with odd C(n) the page's r ∈ {0,1}^{C/2} is undefined
--   - correction: every monotone time-constructible T, C, Q with Q(x) < 2^(x/2) → additionally n + C(n)/2 ≤ K₀·(T(n) + 1); reason: counterexample without it: T(n) = ⌈log₂(n+1)⌉, C(n) the least even number ≥ ⌈log₂ n⌉, Q(x) = ⌈2^{x/2}⌉ − 1, V(x; r) = x[r mod n], Π_Y the strings with at most t ≈ √n/4 zeros, Π_N those with at most t ones. In time polylog(n) no query of length ≥ n can be written. Some r must accept 1ⁿ after reading polylog(n) positions, and zeroing all other positions gives a no-instance accepted with the same r; the proof assumes "T > C without loss of generality" (p.27)
--   - reading: T′ any function with T′(n + C(n)/2) = T(n) → T′ also time-constructible; reason: Definition 4.1 defines the classes for time-constructible functions, and with arbitrary values of T′ off the image of n + C(n)/2 the oracle algorithm would have to recognize that image within them
--   - reading: prRTC^{prcoRTC} with a promise-problem oracle → the oracle algorithm works for every oracle that answers Π′ on its promise and arbitrarily (0 or 1) elsewhere; reason: the standard semantics; the page fixes none
--   - reading: prcoRTC_{Q′}[T′, O(n)] → prcoRTC_{Q′}[T′, C′] for some C′ with C′(m) ≤ K·m, not required to be time-constructible; reason: O(n) names a coin-count function, here existential; footnote 27 calls it an upper bound on the coins
--   - generalization: monotone increasing T → Monotone T (non-decreasing); reason: the proof uses only monotonicity; every strictly increasing T is an instance
--   - reading: "runs in time t" on an unspecified RAM → time at most budget = K·(t+1)·(log₂(n+t+2)+1)^k on the log-cost RAM; reason: the paper fixes no cost model; the log-cost RAM differs from a word RAM by polylogarithmic factors
-- source:
--   Chen, Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027 submission (manuscript sha256 599d0a59…), Lemma 4.16, p.25 (pdf p.27)

import Mathlib
import Definitions.Def_TargetedSamplers_InPrBPTC
import Definitions.Def_TargetedSamplers_TimeConstructible
import Definitions.Def_TargetedSamplers_IsOracleFor

namespace TargetedSamplers

/-- Lemma 4.16 (reducing QD with two-sided error to QD with one-sided error) (Chen, Doron, Ebtehaj,
Tell, Targeted Samplers, STOC 2027 submission, manuscript sha256 599d0a59…, p.25). For monotone
increasing time-constructible `T, C, Q : ℕ → ℕ` with `Q(x) < 2^{x/2}` for every `x`,
`prBPTC_Q[T, C] ⊆ prRTC_{Q′}[T, C/2]^{prcoRTC_{Q′}[T′, O(n)]}`, where `Q′(x) = Q(2x)` and `T′` is any
function with `T′(n + C(n)/2) = T(n)`; the oracle is queried once, on an instance of length
`ℓ(n) = n + C(n)/2`.

**Formalization Note** The oracle class is a promise problem `Π′ ∈ prcoRTC_{Q′}[T′, C′]` with
`C′(m) ≤ K·m`; the outer algorithm must work for every oracle answering `Π′` on its promise and
arbitrarily elsewhere. `C(n)` is even (the page splits `r` into halves and uses `C/2` coins). `T′` is
time-constructible, as Definition 4.1 requires of the functions indexing a class. Time is `budget`.

Corrected: `n + C(n)/2 ≤ K·(T(n) + 1)` is assumed, since the algorithm must write a query of that
length (the proof, p.27, says "`T > C` without loss of generality"). Without it the lemma is false.
Take `T(n) = ⌈log₂(n + 1)⌉`, `C(n)` the least even number `≥ ⌈log₂ n⌉`, `Q(x) = ⌈2^{x/2}⌉ − 1`,
`V(x; r) = x[r mod n]`, `Π_Y` the strings with at most `t ≈ √n/4` zeros and `Π_N` those with at most
`t` ones. In time `polylog(n)` no query can be written. Some `r` must accept `1ⁿ`, after reading
`polylog(n)` positions; zeroing every other position gives a no-instance accepted with the same `r`. -/
theorem lemma_4_16 (T C Q : ℕ → ℕ) (hTm : Monotone T) (hCm : Monotone C) (hQm : Monotone Q)
    (hTc : TimeConstructible T) (hCc : TimeConstructible C) (hQc : TimeConstructible Q)
    (hQlt : ∀ x : ℕ, (Q x : ℝ) < (2 : ℝ) ^ ((x : ℝ) / 2)) (hCeven : ∀ n, Even (C n))
    (hTC : ∃ K₀ : ℕ, ∀ n, n + C n / 2 ≤ K₀ * (T n + 1))
    (T' : ℕ → ℕ) (hT'c : TimeConstructible T') (hT' : ∀ n, T' (n + C n / 2) = T n) :
    ∀ L : KarpLiptonOM.PromiseProblem, InPrBPTC (fun c => (Q c : ℝ)) T C L →
      ∃ L' : KarpLiptonOM.PromiseProblem,
        (∃ (C' : ℕ → ℕ) (K : ℕ), (∀ m, C' m ≤ K * m) ∧
          InPrCoRTC (fun c => (Q (2 * c) : ℝ)) T' C' L') ∧
        ∃ A : Program,
          IsRTCAlgRel (fun c => (Q (2 * c) : ℝ)) T (fun n => C n / 2) L
            (fun O => IsOracleFor L' O) A ∧
          ∀ O, IsOracleFor L' O → ∀ x r : List Bool, r.length = C x.length / 2 →
            (A.queriesAsked ⟨x, r, [], O⟩).length = 1 ∧
            ∀ q ∈ A.queriesAsked ⟨x, r, [], O⟩, q.length = x.length + C x.length / 2 := by sorry

end TargetedSamplers
