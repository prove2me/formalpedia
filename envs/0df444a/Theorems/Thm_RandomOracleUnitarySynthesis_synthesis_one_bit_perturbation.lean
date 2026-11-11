-- Prove2me | Theorems.Thm_RandomOracleUnitarySynthesis_synthesis_one_bit_perturbation
-- name    : RandomOracleUnitarySynthesis.synthesis_one_bit_perturbation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:56:02.719893+00:00
-- url     : https://prove2.me/theorems/b7d40f4b-fb92-42dc-b96a-19f7be282608
-- title:
--   Lemma 4.8 — One-bit perturbation
-- statement:
--   For a fixed circuit, truth table $f$, and oracle input $x$, let $f'$ equal $f$ except that its value at $x$ is flipped. With $A_f=J^\dagger W_fJ$ and the influences from Definition 4.6,
--
--   $$\|A_{f'}-A_f\|_F^2\le4w_f(x)w_{f'}(x).$$
--
--   This bounds the effect of a single truth-table change using the influences of the two distinct oracles.
--
--   Differences from the source:
--   - encoding: binary computational bases, Boolean truth tables, and the stated register inequalities → Fin n → Fin 2 bases, Bool-valued truth tables, and a circuit type carrying n ≤ m and m₀ ≤ m; reason: these are bijective finite encodings of exactly the source registers and functions
-- source:
--   Andrew Huang, Akshar Ramkumar, John Wright, STOC 2027 submission #157 (October 2026), Lemma 4.8, printed p. 19 (PDF p. 21); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/157.pdf#page=21; PDF SHA256 2f2d7fa67fe2665257ec12cb0d11d7e2a80752cdecc0484b26a311d1223c5d11

import Definitions.Def_RandomOracleUnitarySynthesis_synthesis_circuit

open scoped Matrix ComplexConjugate
open MeasureTheory Filter Classical
noncomputable section

namespace RandomOracleUnitarySynthesis

theorem synthesis_one_bit_perturbation {n m m₀ k : ℕ}
    (C : synthesis_Circuit n m m₀ k) (f : synthesis_Oracle m₀) (x : synthesis_Bits m₀) :
    QAlgorithms.frobNorm (synthesis_A C (synthesis_flip f x) - synthesis_A C f)^2 ≤
      4 * synthesis_influence C f x * synthesis_influence C (synthesis_flip f x) x := by sorry

end RandomOracleUnitarySynthesis
