-- Prove2me | Theorems.Thm_RandomOracleUnitarySynthesis_synthesis_total_influence
-- name    : RandomOracleUnitarySynthesis.synthesis_total_influence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:56:19.973601+00:00
-- url     : https://prove2.me/theorems/64ef841d-a75f-4c35-85c2-90f8899a5f0f
-- title:
--   Lemma 4.7 — Total influence
-- statement:
--   Let $V_0,\ldots,V_k$ be a fixed circuit on $m$ qubits, with $n$ system qubits and oracle length $m_0$, and let $f$ be any Boolean truth table. For the two-sided influence $w_f(x)$ of Definition 4.6,
--
--   $$\sum_{x\in\{0,1\}^{m_0}}w_f(x)=2k\,2^n.$$
--
--   This deterministic identity controls the total influence over every oracle input; no randomness in $f$ is assumed.
--
--   Differences from the source:
--   - encoding: binary computational bases, Boolean truth tables, and the stated register inequalities → Fin n → Fin 2 bases, Bool-valued truth tables, and a circuit type carrying n ≤ m and m₀ ≤ m; reason: these are bijective finite encodings of exactly the source registers and functions
-- source:
--   Andrew Huang, Akshar Ramkumar, John Wright, STOC 2027 submission #157 (October 2026), Lemma 4.7, printed p. 18 (PDF p. 20); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/157.pdf#page=20; PDF SHA256 2f2d7fa67fe2665257ec12cb0d11d7e2a80752cdecc0484b26a311d1223c5d11

import Definitions.Def_RandomOracleUnitarySynthesis_synthesis_circuit

open scoped Matrix ComplexConjugate
open MeasureTheory Filter Classical
noncomputable section

namespace RandomOracleUnitarySynthesis

theorem synthesis_total_influence {n m m₀ k : ℕ}
    (C : synthesis_Circuit n m m₀ k) (f : synthesis_Oracle m₀) :
    (∑ x, synthesis_influence C f x) = 2 * (k : ℝ) * (2 : ℝ)^n := by sorry

end RandomOracleUnitarySynthesis
