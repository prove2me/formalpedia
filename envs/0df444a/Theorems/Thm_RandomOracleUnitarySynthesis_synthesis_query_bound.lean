-- Prove2me | Theorems.Thm_RandomOracleUnitarySynthesis_synthesis_query_bound
-- name    : RandomOracleUnitarySynthesis.synthesis_query_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:57:15.016099+00:00
-- url     : https://prove2.me/theorems/837ed6d6-9569-4a4f-9c58-09c763e1c513
-- title:
--   Theorem 4.1 — Random-oracle unitary synthesis query bound
-- statement:
--   There is an absolute constant $c>0$ such that the following holds for every synthesis family. At system size $n$, the circuit has arbitrary $m(n)\ge n$, $m_0(n)\le m(n)$, fixed gates, and eventually at least one query. Its random-oracle channel admits the channel-valued Haar coupling of Definition 3.6 with expected diamond error at most $0\le\varepsilon(n)<1$. Put $N(n)=2^n$ and $a(n)=1-\varepsilon(n)$. If $N(n)^2a(n)\to+\infty$, then eventually
--
--   $$k(n)^2a(n)^{-6}\ge cN(n).$$
--
--   In particular, for every $B>0$ and $d\ge0$ with $a(n)^{-1}\le B(n+1)^d$ eventually, there are $B'>0$ and $d'\ge0$ such that eventually
--
--   $$k(n)\ge\frac{\sqrt{2^n}}{B'(n+1)^{d'}}.$$
--
--   The first constant is independent of the family, circuit, and ancilla count. The eventual thresholds and polynomial constants may depend on the family and the polynomial accuracy bound. Both conclusions belong to this single goal.
--
--   Differences from the source:
--   - encoding: binary computational bases, Boolean truth tables, and the stated register inequalities → Fin n → Fin 2 bases, Bool-valued truth tables, and a circuit type carrying n ≤ m and m₀ ≤ m; reason: these are bijective finite encodings of exactly the source registers and functions
--   - encoding: ω and O/Ω notation for synthesis algorithms → eventually quantified families, N²(1−ε) → +∞, and an absolute positive constant before all family parameters; reason: this spells out the source asymptotic quantifiers and permits arbitrary ancilla growth
--   - encoding: a nonnegative expected diamond-distance bound in a joint channel distribution → a probability coupling on Borel channel coordinates and a nonnegative Lebesgue integral; reason: it preserves arbitrary dependence and the exact two channel marginals without Bochner-integral defaults
--   - encoding: inverse-polynomial accuracy and query lower bound → arbitrary positive polynomial prefactors and nonnegative real degrees with n+1 as argument; reason: eventually these describe exactly the same polynomial bounds, including the boundary n=0
-- source:
--   Andrew Huang, Akshar Ramkumar, John Wright, STOC 2027 submission #157 (October 2026), Theorem 4.1, printed p. 16 (PDF p. 18); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/157.pdf#page=18; PDF SHA256 2f2d7fa67fe2665257ec12cb0d11d7e2a80752cdecc0484b26a311d1223c5d11

import Definitions.Def_RandomOracleUnitarySynthesis_synthesis_family

open scoped Matrix ComplexConjugate
open MeasureTheory Filter Classical
noncomputable section

namespace RandomOracleUnitarySynthesis

theorem synthesis_query_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ (m m₀ k : ℕ → ℕ)
      (C : (n : ℕ) → synthesis_Circuit n (m n) (m₀ n) (k n)) (ε : ℕ → ℝ),
      synthesis_Admissible m m₀ k C ε → synthesis_GapRegime ε →
      (∀ᶠ n : ℕ in atTop, c * (2 : ℝ)^n ≤ (k n : ℝ)^2 * ((1-ε n)⁻¹)^6) ∧
      (∀ B d : ℝ, 0 < B → 0 ≤ d → synthesis_PolynomialGap ε B d →
        ∃ B' d' : ℝ, 0 < B' ∧ 0 ≤ d' ∧
          ∀ᶠ n : ℕ in atTop, Real.sqrt ((2 : ℝ)^n) /
            (B' * Real.rpow ((n : ℝ)+1) d') ≤ (k n : ℝ)) := by sorry

end RandomOracleUnitarySynthesis
