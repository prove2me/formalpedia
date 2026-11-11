-- Prove2me | Theorems.Thm_RandomOracleUnitarySynthesis_synthesis_resampling_energy
-- name    : RandomOracleUnitarySynthesis.synthesis_resampling_energy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:57:00.690963+00:00
-- url     : https://prove2.me/theorems/a6e674fa-596d-47d9-93a5-4eb68d7459be
-- title:
--   Lemma 4.9 — Reversible resampling energy
-- statement:
--   Fix a circuit and $0<r\le1$. Start with a uniform truth table $f=f_0$, then run the concrete symmetric resampling procedure from the proof of Theorem 4.5, with independent fair replacement bits. If its successive functions are $f_1,\ldots,f_{M_0}=f_S$, then
--
--   $$\mathbb E\|A_f-A_{f_S}\|_F^2\le2\sum_{i=1}^{M_0}\mathbb E\|A_{f_i}-A_{f_{i-1}}\|_F^2.$$
--
--   The statement concerns this particular adaptive procedure and makes no energy-invariant assumption about an arbitrary path.
--
--   Differences from the source:
--   - encoding: binary computational bases, Boolean truth tables, and the stated register inequalities → Fin n → Fin 2 bases, Bool-valued truth tables, and a circuit type carrying n ≤ m and m₀ ≤ m; reason: these are bijective finite encodings of exactly the source registers and functions
--   - encoding: uniform finite expectations → normalized finite sums and genuine PMF expectations; reason: the truth-table and seed sets are finite and nonempty, so the sums equal the source expectations
--   - encoding: the procedure with threshold r²/(8k) in the positive-query proof → the same procedure, with threshold zero at k=0 and fully independent resampling; reason: the zero-query compressed block is constant and this defines the boundary without division by zero
-- source:
--   Andrew Huang, Akshar Ramkumar, John Wright, STOC 2027 submission #157 (October 2026), Lemma 4.9, printed p. 21 (PDF p. 23); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/157.pdf#page=23; PDF SHA256 2f2d7fa67fe2665257ec12cb0d11d7e2a80752cdecc0484b26a311d1223c5d11

import Definitions.Def_RandomOracleUnitarySynthesis_synthesis_resampling

open scoped Matrix ComplexConjugate
open MeasureTheory Filter Classical
noncomputable section

namespace RandomOracleUnitarySynthesis

theorem synthesis_resampling_energy {n m m₀ k : ℕ}
    (C : synthesis_Circuit n m m₀ k) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    synthesis_energy C (synthesis_resample C r) ≤
      2 * ∑ i : Fin (Fintype.card (synthesis_Bits m₀)), synthesis_stepEnergy C r i.val := by sorry

end RandomOracleUnitarySynthesis
