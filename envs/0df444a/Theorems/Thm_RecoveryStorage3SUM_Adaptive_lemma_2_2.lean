-- Prove2me | Theorems.Thm_RecoveryStorage3SUM_Adaptive_lemma_2_2
-- name    : RecoveryStorage3SUM.Adaptive.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:09:55.800896+00:00
-- url     : https://prove2.me/theorems/a3f1ce12-b29e-4778-a858-5e5a78d44dd9
-- title:
--   Lemma 2.2 — two fixed integers collide modulo a random prime with probability $O(\log n/R)$
-- statement:
--   Let $u\ne v$ be integers, and let $R\ge2$ be a real cutoff, with $|u|,|v|,R\le H(n+2)^\kappa$. For a uniformly random prime $p\in[R,2R]$,
--   $$\Pr[u\equiv_p v]\le \frac{C\log(n+2)}{R},$$
--   where $C$ depends only on $H$ and $\kappa$. The prime support is exactly the primes between $\lceil R\rceil$ and $\lfloor2R\rfloor$, inclusive.
--
--   This is the collision estimate behind the load bound, the clean-run bound, and the bound on $|M_r|$.
--
--   Differences from the source:
--   - encoding: integers bounded by $n^{O(1)}$ (standing assumption, §2) → $|x|\le H(n+2)^\kappa$ with $H,\kappa$ fixed first; reason: same class of inputs; constants are chosen after them
--   - encoding: $O(\log n/R)$ → $C\log(n+2)/R$; reason: $\log(n+2)$ stays positive at $n\le1$; for $n\ge2$ the two agree up to a constant
--   - encoding: a uniform prime in the closed real interval $[R,2R]$ → uniform primes in the integer interval $[\lceil R\rceil,\lfloor2R\rfloor]$, for every real $R\ge2$; reason: these are exactly the integer primes in the source interval; no cutoff is restricted or moved
-- source:
--   Amir Carmel, Yakov Kosoburd, Robert Krauthgamer, STOC 2027 submission #561 (October 2026), Lemma 2.2, p.6

import Mathlib
import Definitions.Def_RecoveryStorage3SUM_Adaptive_Protocol
import Definitions.Def_RecoveryStorage3SUM_Adaptive_Laws

set_option autoImplicit false

namespace RecoveryStorage3SUM.Adaptive

/-- Lemma 2.2, p.6: for `u ≠ v` bounded by `n^{O(1)}` and a uniform prime `p ∈ [R, 2R]`,
`2 ≤ R ≤ n^{O(1)}`, one has `Pr[u ≡_p v] = O(log n / R)`. The cutoff `R` may be real;
the prime support uses the exact integer endpoints `⌈R⌉` and `⌊2R⌋`. -/
theorem lemma_2_2 (H κ : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (R : ℝ) (u v : ℤ), u ≠ v →
      PolyBounded H κ n u → PolyBounded H κ n v →
      2 ≤ R → R ≤ (H : ℝ) * ((n : ℝ) + 2) ^ κ →
      unifProb ((Finset.Icc ⌈R⌉₊ ⌊2 * R⌋₊).filter Nat.Prime) (fun p => (p : ℤ) ∣ u - v) ≤
        C * Real.log ((n : ℝ) + 2) / R := by sorry

end RecoveryStorage3SUM.Adaptive
