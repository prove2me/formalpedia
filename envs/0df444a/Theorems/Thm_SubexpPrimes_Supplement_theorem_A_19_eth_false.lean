-- Prove2me | Theorems.Thm_SubexpPrimes_Supplement_theorem_A_19_eth_false
-- name    : SubexpPrimes.Supplement.theorem_A_19_eth_false
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:49:06.117315+00:00
-- url     : https://prove2.me/theorems/ce9e98f5-a740-43e2-825e-9027cfe9daf2
-- title:
--   Theorem A.19 — counting 3-CNF solutions in time $2^{\varepsilon n}\mathrm{poly}(|\varphi|)$ for every $\varepsilon>0$; ETH is false
-- statement:
--   For every real $\varepsilon>0$ there are a deterministic machine and a constant $K$ such that, for every $n$ and every 3-CNF formula $\varphi$ on $n$ variables (every clause has at most three literals), the machine, given the encoding of $\varphi$, outputs the number $\#\varphi$ of satisfying assignments of $\varphi$ within
--
--   $$
--   K\,(|\varphi|+1)^K\,2^{\varepsilon n}
--   $$
--
--   steps, where $|\varphi|$ is the length of the encoding. In particular, the Exponential Time Hypothesis is false.
--
--   This places the paper's contraction lemma in line with the refutation of ETH that motivated it.
--
--   **Formalization Note** No space bound is claimed. The machine depends on $\varepsilon$ only. The formula type, its encoding and the count are those of the published `SubexponentialSAT` definitions; ETH is the Supplement definition over the same machine model.
--
--   Differences from the source:
--   - encoding: time 2^{εn} poly(|φ|) → K (|φ|+1)^K 2^{εn} steps, |φ| the length of encodeCNF φ; reason: one constant for the polynomial; same instances
--   - encoding: 3-CNF formula on n variables → SAT.CNF (Fin n) with SAT.WidthAtMost 3; reason: clauses of at most three literals, as in Lemma A.21
--   - reading: ETH: no algorithm decides 3-CNF satisfiability in time 2^{δn} poly(|φ|) → ETH quantified over PrimitiveMachines of the SubexponentialSAT model, output the bit [0 < count φ]; reason: the paper names no machine model; the base mission's model
-- source:
--   Gajulapalli, Deterministic Construction of Primes in Subexponential Time (manuscript, sha256 6ad4d3de…), Theorem A.19, p.72 (PDF p.74); proof p.73

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_SubexpPrimes_Supplement_ETH

set_option autoImplicit false

namespace SubexpPrimes.Supplement

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- **Theorem A.19** — Gajulapalli, *Deterministic Construction of Primes in Subexponential Time*
(manuscript, sha256 6ad4d3de…), p.72.

For every `ε > 0` there is a deterministic algorithm that, given a 3-CNF formula `φ` on `n` variables,
counts its satisfying assignments in time `2^{εn} poly(|φ|)`. In particular, ETH is false.

**Formalization Note.** For each real `ε > 0` one machine `M` and one constant `K` (chosen after `ε`,
before `n` and `φ`) serve every `n` and every CNF `φ` on `Fin n` of width at most 3; on input
`Encoding.encodeCNF φ` it halts with `countWord (SAT.count φ)` within `K (|φ| + 1)^K 2^{ε n}` steps,
`|φ|` being the length of the encoding. No space bound is claimed, as in the source (`HaltsWithin`).
`ETH` is the Supplement definition over the same machine model. -/
theorem theorem_A_19_eth_false :
    (∀ ε : ℝ, 0 < ε →
      ∃ (M : PrimitiveMachine) (out : Fin M.tapeCount) (K : ℕ),
        ∀ (n : ℕ) (φ : SAT.CNF (Fin n)), SAT.WidthAtMost 3 φ →
          HaltsWithin M out (Encoding.encodeCNF φ) (countWord (SAT.count φ))
            ((K : ℝ) * (((Encoding.encodeCNF φ).length : ℝ) + 1) ^ K *
              (2 : ℝ) ^ (ε * (n : ℝ)))) ∧
    ¬ ETH := by sorry

end SubexpPrimes.Supplement
