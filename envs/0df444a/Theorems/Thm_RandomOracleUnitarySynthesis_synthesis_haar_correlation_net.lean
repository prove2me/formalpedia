-- Prove2me | Theorems.Thm_RandomOracleUnitarySynthesis_synthesis_haar_correlation_net
-- name    : RandomOracleUnitarySynthesis.synthesis_haar_correlation_net
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:57:16.819644+00:00
-- url     : https://prove2.me/theorems/efa91915-4d93-4d34-9941-28e8da92a88d
-- title:
--   Lemma 4.12 — Haar correlation net
-- statement:
--   There is an absolute $B>0$ such that every admissible synthesis family with $a(n)=1-\varepsilon(n)$ and $N(n)^2a(n)\to+\infty$ has, for all sufficiently large $n$, a finite nonempty set $T$ of Hermitian contractions and a nonidentity Pauli operator $Q$ satisfying
--
--   $$\log_2|T|\le B\frac{Nk^2}{a^4},\qquad \Pr_{U\sim\mathrm{Haar}}\!\left[\max_{A\in T}\frac1N\operatorname{tr}(AU^\dagger Q U)\ge\frac a8\right]\ge\frac a8.$$
--
--   Both $T$ and $Q$ are fixed before drawing $U$. The statement retains the expected-channel coupling and the complete near-one-error regime.
--
--   Differences from the source:
--   - encoding: binary computational bases, Boolean truth tables, and the stated register inequalities → Fin n → Fin 2 bases, Bool-valued truth tables, and a circuit type carrying n ≤ m and m₀ ≤ m; reason: these are bijective finite encodings of exactly the source registers and functions
--   - encoding: ω and O/Ω notation for synthesis algorithms → eventually quantified families, N²(1−ε) → +∞, and an absolute positive constant before all family parameters; reason: this spells out the source asymptotic quantifiers and permits arbitrary ancilla growth
--   - encoding: minimum or maximum over a finite operator set → a nonempty Finset and equivalent universal or existential membership events; reason: finite nonemptiness ensures attainment and avoids default values of real extrema or log cardinality
--   - encoding: ordinary real trace of products of Hermitian operators → the real part of the ordinary complex trace; reason: conjugating and cycling the trace proves its reality without adding a hypothesis
--   - encoding: probability for a normalized Haar random full complex unitary → evaluation of Borel Haar probability with ENNReal.ofReal thresholds; reason: the measure is an actual probability and all thresholds are nonnegative in the stated domain
--   - encoding: a nonnegative expected diamond-distance bound in a joint channel distribution → a probability coupling on Borel channel coordinates and a nonnegative Lebesgue integral; reason: it preserves arbitrary dependence and the exact two channel marginals without Bochner-integral defaults
-- source:
--   Andrew Huang, Akshar Ramkumar, John Wright, STOC 2027 submission #157 (October 2026), Lemma 4.12, printed p. 28 (PDF p. 30); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/157.pdf#page=30; PDF SHA256 2f2d7fa67fe2665257ec12cb0d11d7e2a80752cdecc0484b26a311d1223c5d11

import Definitions.Def_RandomOracleUnitarySynthesis_synthesis_family

open scoped Matrix ComplexConjugate
open MeasureTheory Filter Classical
noncomputable section

namespace RandomOracleUnitarySynthesis

theorem synthesis_haar_correlation_net :
    ∃ B : ℝ, 0 < B ∧ ∀ (m m₀ k : ℕ → ℕ)
      (C : (n : ℕ) → synthesis_Circuit n (m n) (m₀ n) (k n)) (ε : ℕ → ℝ),
      synthesis_Admissible m m₀ k C ε → synthesis_GapRegime ε →
      ∀ᶠ n : ℕ in atTop, ∃ T : Finset (synthesis_Mat n), T.Nonempty ∧
        (∀ A ∈ T, A.IsHermitian ∧ synthesis_IsContraction A) ∧
        Real.logb 2 (T.card : ℝ) ≤ B * (2 : ℝ)^n * (k n : ℝ)^2 / (1-ε n)^4 ∧
        ∃ Q : synthesis_Pauli n, Q ≠ (fun _ => 0) ∧
          ENNReal.ofReal ((1-ε n)/8) ≤ (synthesis_haar n)
            {U | ∃ A ∈ T, (1-ε n)/8 ≤ synthesis_correlation A Q U} := by sorry

end RandomOracleUnitarySynthesis
