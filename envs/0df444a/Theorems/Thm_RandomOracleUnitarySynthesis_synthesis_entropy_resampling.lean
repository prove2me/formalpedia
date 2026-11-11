-- Prove2me | Theorems.Thm_RandomOracleUnitarySynthesis_synthesis_entropy_resampling
-- name    : RandomOracleUnitarySynthesis.synthesis_entropy_resampling
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:57:06.056131+00:00
-- url     : https://prove2.me/theorems/56eef8e8-990b-4eef-8be1-79d9e69fb9a8
-- title:
--   Theorem 4.5 — Entropy-preserving resampling
-- statement:
--   Fix the full circuit $V_0,\ldots,V_k$ with $n\le m$ and $m_0\le m$, and put $N=2^n$, $M_0=2^{m_0}$. For every $0<r\le1$ there is a finite randomized algorithm taking a uniform Boolean function $f$ to a subset $S$ of oracle inputs and a function $f_S$, such that
--
--   $$H(f_S\mid f)\ge M_0-\frac{32k^2N}{r^2},\qquad \mathbb E\|A_f-A_{f_S}\|_F^2\le2Nr^2.$$
--
--   Entropy is in bits. Both conclusions refer to the same randomized algorithm, with no running-time constraint and no positive-query restriction.
--
--   Differences from the source:
--   - encoding: binary computational bases, Boolean truth tables, and the stated register inequalities → Fin n → Fin 2 bases, Bool-valued truth tables, and a circuit type carrying n ≤ m and m₀ ≤ m; reason: these are bijective finite encodings of exactly the source registers and functions
--   - encoding: uniform finite expectations → normalized finite sums and genuine PMF expectations; reason: the truth-table and seed sets are finite and nonempty, so the sums equal the source expectations
--   - encoding: a randomized algorithm producing a subset and function → an existential finite PMF kernel producing the same two outputs; reason: every finite-output randomized procedure has such a kernel, and conversely the kernel is the allowed randomized procedure
-- source:
--   Andrew Huang, Akshar Ramkumar, John Wright, STOC 2027 submission #157 (October 2026), Theorem 4.5, printed p. 17 (PDF p. 19); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/157.pdf#page=19; PDF SHA256 2f2d7fa67fe2665257ec12cb0d11d7e2a80752cdecc0484b26a311d1223c5d11

import Definitions.Def_RandomOracleUnitarySynthesis_synthesis_resampling

open scoped Matrix ComplexConjugate
open MeasureTheory Filter Classical
noncomputable section

namespace RandomOracleUnitarySynthesis

theorem synthesis_entropy_resampling {n m m₀ k : ℕ}
    (C : synthesis_Circuit n m m₀ k) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ K : synthesis_Resampler m₀,
      (2 : ℝ)^m₀ - 32 * (k : ℝ)^2 * (2 : ℝ)^n / r^2 ≤ synthesis_conditionalEntropy K ∧
      synthesis_energy C K ≤ 2 * (2 : ℝ)^n * r^2 := by sorry

end RandomOracleUnitarySynthesis
