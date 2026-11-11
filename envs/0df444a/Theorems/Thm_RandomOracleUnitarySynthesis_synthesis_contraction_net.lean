-- Prove2me | Theorems.Thm_RandomOracleUnitarySynthesis_synthesis_contraction_net
-- name    : RandomOracleUnitarySynthesis.synthesis_contraction_net
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:56:12.523982+00:00
-- url     : https://prove2.me/theorems/4e6cf39c-c594-4693-91b0-0f60ffdfb9ad
-- title:
--   Corollary 4.10 — Small contraction net with Hermitian refinement
-- statement:
--   There is an absolute constant $B>0$ with the following property. Fix any circuit with $k\ge1$ queries and any $0<d<2$, $0<\zeta<1$. There is a finite nonempty set $T$ of spectral-norm contractions such that
--
--   $$\log_2|T|\le B\frac{Nk^2}{\zeta^2d^2},\qquad \Pr_f\!\left[\min_{A\in T}\|A-A_f\|_F>d\sqrt N\right]\le\zeta.$$
--
--   If every $A_f$ is Hermitian, the witnessing set $T$ consists of Hermitian contractions. The set is chosen before drawing $f$. This is the covering statement for the full family of compressed circuit blocks.
--
--   Differences from the source:
--   - encoding: binary computational bases, Boolean truth tables, and the stated register inequalities → Fin n → Fin 2 bases, Bool-valued truth tables, and a circuit type carrying n ≤ m and m₀ ≤ m; reason: these are bijective finite encodings of exactly the source registers and functions
--   - encoding: uniform finite expectations → normalized finite sums and genuine PMF expectations; reason: the truth-table and seed sets are finite and nonempty, so the sums equal the source expectations
--   - encoding: minimum or maximum over a finite operator set → a nonempty Finset and equivalent universal or existential membership events; reason: finite nonemptiness ensures attainment and avoids default values of real extrema or log cardinality
--   - encoding: an O(Nk²/(ζ²d²)) bound → one absolute positive B quantified before dimensions, circuits, d, and ζ; reason: the implicit constant is uniform over exactly those source parameters
-- source:
--   Andrew Huang, Akshar Ramkumar, John Wright, STOC 2027 submission #157 (October 2026), Corollary 4.10, printed p. 24 (PDF p. 26); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/157.pdf#page=26; PDF SHA256 2f2d7fa67fe2665257ec12cb0d11d7e2a80752cdecc0484b26a311d1223c5d11

import Definitions.Def_RandomOracleUnitarySynthesis_synthesis_circuit

open scoped Matrix ComplexConjugate
open MeasureTheory Filter Classical
noncomputable section

namespace RandomOracleUnitarySynthesis

theorem synthesis_contraction_net :
    ∃ B : ℝ, 0 < B ∧ ∀ (n m m₀ k : ℕ) (C : synthesis_Circuit n m m₀ k),
      1 ≤ k → ∀ d : ℝ, 0 < d → d < 2 → ∀ ζ : ℝ, 0 < ζ → ζ < 1 →
      ∃ T : Finset (synthesis_Mat n), T.Nonempty ∧
        (∀ A ∈ T, synthesis_IsContraction A) ∧
        Real.logb 2 (T.card : ℝ) ≤ B * (2 : ℝ)^n * (k : ℝ)^2 / (ζ^2 * d^2) ∧
        synthesis_average (fun f : synthesis_Oracle m₀ =>
          if ∀ A ∈ T, d * Real.sqrt ((2 : ℝ)^n) < QAlgorithms.frobNorm (A - synthesis_A C f)
          then (1 : ℝ) else 0) ≤ ζ ∧
        ((∀ f, (synthesis_A C f).IsHermitian) → ∀ A ∈ T, A.IsHermitian) := by sorry

end RandomOracleUnitarySynthesis
