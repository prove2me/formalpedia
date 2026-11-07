-- Prove2me | Theorems.Thm_TargetedSamplers_theorem_4_14
-- name    : TargetedSamplers.theorem_4_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:07:43.054295+00:00
-- url     : https://prove2.me/theorems/19ced692-e75f-42d8-bb56-7438ba392689
-- title:
--   Theorem 4.14 — fast condenser for subconstant rate inputs
-- statement:
--   There is a universal constant $K$ such that for all constants $\epsilon,\gamma\in(0,1)$ there are a constant $\xi$ with $0<\xi\le K\epsilon^3$ and functions
--   $$\mathrm{Con}_n:\{0,1\}^n\times\{0,1\}^{d}\to\{0,1\}^{m},\qquad d\le\epsilon\log_2n+O(1),\quad m=\lceil n^{1-\epsilon^2/4}\rceil,$$
--   such that every $\mathrm{Con}_n$ is an $[n^{-\xi}\mapsto1-\epsilon]_{\sim\gamma}$-condenser and the multiset $\{\mathrm{Con}_n(x;s):s\in\{0,1\}^d\}$ is computable in time $O(n^{1+K\epsilon})$.
--
--   With Theorem 4.15 this gives the overhead-free error reduction of Theorem 4.2.
--
--   Differences from the source:
--   - reading: ξ = O(ϵ³), time O(n^{1+O(ϵ)}) → one universal K with 0 < ξ ≤ Kϵ³ and exponent 1 + Kϵ; reason: constants of O(·) do not depend on ϵ, γ; ξ = 0 would make the input rate 1
--   - encoding: d = ϵ·log(n) + O(1) → d(n) ≤ ϵ log₂ n + K_d; reason: a condenser with a shorter seed gives one with any longer seed (ignore the extra bits), so only the upper bound matters
--   - encoding: m = n^{1−ϵ²/4} → m = ⌈n^{1−ϵ²/4}⌉; reason: integer output length
--   - encoding: the multiset {Conₙ(x;s)} is computable → the program prints the strings in some order whose multiset is that multiset; reason: a multiset has no order
--   - reading: "runs in time t" on an unspecified RAM → time at most budget = K·(t+1)·(log₂(n+t+2)+1)^k on the log-cost RAM; reason: the paper fixes no cost model; the log-cost RAM differs from a word RAM by polylogarithmic factors
--   - reading: γ-close: "L1 norm (i.e. statistical distance)" → statistical distance ½‖P−Q‖₁ ≤ γ; reason: the page equates the two; statistical distance is the standard notion for condensers
-- source:
--   Chen, Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027 submission (manuscript sha256 599d0a59…), Theorem 4.14, p.24 (pdf p.26); Theorem C.2, p.96 (pdf p.98)

import Mathlib
import Definitions.Def_TargetedSamplers_IsCondenser
import Definitions.Def_TargetedSamplers_Machine
import Definitions.Def_TargetedSamplers_encInput

namespace TargetedSamplers

/-- Theorem 4.14 (Fast Condenser for Subconstant Rate Inputs) (Chen, Doron, Ebtehaj, Tell, Targeted
Samplers, STOC 2027 submission, manuscript sha256 599d0a59…, p.24; proof as Theorem C.2, p.96). For
any two constants `ϵ, γ ∈ (0,1)` there are a constant `ξ = O(ϵ³)` and a family
`Conₙ : {0,1}ⁿ × {0,1}^{d = ϵ·log n + O(1)} → {0,1}^{m = n^{1−ϵ²/4}}` of
`[n^{−ξ} ↦ 1 − ϵ]_{∼γ}`-condensers such that the multiset `{Conₙ(x; s) : s ∈ {0,1}^d}` is computable
in time `O(n^{1+O(ϵ)})`.

**Formalization Note** The constant `K` of `O(ϵ³)` and of the exponent `O(ϵ)` is universal, chosen
before `ϵ, γ`; `0 < ξ`. `d = ϵ log₂ n + O(1)` is stated as `d(n) ≤ ϵ log₂ n + K_d` (extra seed bits
can be ignored, so a shorter seed is never worse); `m = ⌈n^{1−ϵ²/4}⌉`. Time is `budget`, and the
multiset is printed in some order. -/
theorem theorem_4_14 : ∃ K : ℝ, 0 < K ∧ ∀ ϵ γ : ℝ, 0 < ϵ → ϵ < 1 → 0 < γ → γ < 1 →
    ∃ ξ : ℝ, 0 < ξ ∧ ξ ≤ K * ϵ ^ 3 ∧
    ∃ (d m : ℕ → ℕ) (Kd : ℝ)
      (Con : (n : ℕ) → (Fin n → Bool) → (Fin (d n) → Bool) → Fin (m n) → Bool),
      (∀ n : ℕ, (d n : ℝ) ≤ ϵ * Real.logb 2 n + Kd) ∧
      (∀ n : ℕ, m n = ⌈(n : ℝ) ^ (1 - ϵ ^ 2 / 4)⌉₊) ∧
      (∀ n : ℕ, IsCondenser ((n : ℝ) ^ (-ξ)) (1 - ϵ) γ (Con n)) ∧
      ∃ (P : Program) (K' k : ℕ), ∀ x : List Bool,
        P.OutputsMultisetIn (Tapes.ofInput x)
          (budget K' k ⌈(x.length : ℝ) ^ (1 + K * ϵ)⌉₊ x.length)
          (Finset.univ.val.map fun s => List.ofFn (Con x.length (toVec x) s)) := by sorry

end TargetedSamplers
