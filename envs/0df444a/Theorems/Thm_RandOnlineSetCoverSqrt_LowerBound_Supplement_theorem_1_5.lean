-- Prove2me | Theorems.Thm_RandOnlineSetCoverSqrt_LowerBound_Supplement_theorem_1_5
-- name    : RandOnlineSetCoverSqrt.LowerBound.Supplement.theorem_1_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T05:14:51.132477+00:00
-- url     : https://prove2.me/theorems/6c7015eb-41b7-4ed5-ad62-832e0298d29d
-- title:
--   Theorem 1.5 — $\Omega(m/\log m)$ lower bound for poly($m$)-memory algorithms
-- statement:
--   For every degree $a\in\mathbb N$ there are constants $c>0$ and $m_0$, depending only on $a$, such that for every $m\ge m_0$ and every $S\le m^a$ the following holds. Let $\mathcal A$ be any valid randomized online set-cover algorithm on the canonical known universe $U_m$ (all nonempty incidence patterns over $m$ unit-cost sets, known in advance) that keeps $S$ bits of memory between requests: $2^S$ memory states, arbitrary computation and fresh randomness at each arrival, no access to past requests, the time or its purchases except through the state, and feasibility on every finite request list with probability one. Then there is a fixed nonempty request list $B$ over $U_m$ (repetitions allowed), chosen independently of the coins, with
--   $$c\cdot\frac{m}{\log m}\cdot\operatorname{OPT}(B)\ \le\ \mathbb E\bigl[|X_{|B|}|\bigr],$$
--   where $X_{|B|}$ is the set of all labels the algorithm has bought (including before the first request) and $\log$ is the natural logarithm.
--
--   So every randomized algorithm for unweighted online set cover with $\operatorname{poly}(m)$ memory has competitive ratio $\Omega(m/\log m)=\tilde\Omega(m)$, even in the known-instance model and with unlimited computation between requests.
--
--   Differences from the source:
--   - reading: uses poly(m) memory; competitive ratio Ω(m/log m) → for every degree a there are c > 0 and m₀ (depending on a only) such that every algorithm with S ≤ m^a bits, m ≥ m₀, has a bad input; reason: the Ω constant in the proof depends on the polynomial; any bound S ≤ C·m^a is ≤ m^(a+1) for m ≥ C, so every polynomial is covered
--   - generalization: every algorithm on a known set system → the fixed canonical known universe U_m, with a bad request list for every valid algorithm; reason: a hard input on one fixed known system implies the source lower bound
--   - encoding: memory = information preserved between requests, unlimited computation → 2^S states, an initial law and a time-homogeneous kernel on (state, arriving element) with fresh randomness; purchases recorded outside the state; reason: the paper defines memory this way and its proof simulates the algorithm by passing only the S-bit state, generating random choices privately and storing the purchase vector separately; the kernel does not read the purchase record, but an algorithm that reads its purchases without storing them is simulated with S + m ≤ m^(a+1) state bits (m ≥ 2), which the ∀ a quantifier covers
--   - encoding: positive offline optimum and multiplicative ratio → listOpt of the incidences as a natural number, a nonempty list, and c·(m / log m)·OPT(B) ≤ expected cost; reason: every element of U_m has a nonempty incidence, so OPT(B) is finite and at least 1 for nonempty B; natural log as in the paper
-- source:
--   Ilan Doron-Arad, Joseph (Seffi) Naor, STOC 2027 submission #1160 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1160.pdf, Theorem 1.5, printed p. 3 / PDF p. 4; restated printed p. 18 / PDF p. 19; proof printed p. 19 / PDF p. 20

import Definitions.Def_RandOnlineSetCoverSqrt_LowerBound_Supplement_Memory

namespace RandOnlineSetCoverSqrt.LowerBound.Supplement

/-- Theorem 1.5, printed p. 3 / PDF p. 4 and printed p. 18 / PDF p. 19 (proof PDF p. 20).
"poly(m) memory": for every degree `a`, with constants `c, m₀` depending on `a` only, every
valid algorithm with `S ≤ m ^ a` bits of memory on the known universe `U_m` has a fixed nonempty
request list (repetitions allowed) on which its expected cost is at least `c · (m / log m) · OPT`.
Natural logarithm. -/
theorem theorem_1_5 :
    ∀ a : ℕ, ∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ S : ℕ, S ≤ m ^ a →
      ∀ A : MemAlg m S, A.IsValid →
      ∃ B : List (Element m), B ≠ [] ∧
        c * ((m : ℝ) / Real.log (m : ℝ)) * (listOptNat B : ℝ) ≤ A.expectedCost B := by sorry

end RandOnlineSetCoverSqrt.LowerBound.Supplement
