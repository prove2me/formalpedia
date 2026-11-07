-- Prove2me | Theorems.Thm_QAdvFew_PoQOracle_lemma_4_2
-- name    : QAdvFew.PoQOracle.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:55:56.045677+00:00
-- url     : https://prove2.me/theorems/b93735bf-9e6c-4f93-9080-5b74d1da63da
-- title:
--   Lemma 4.2 — $\mathsf P^O=\mathsf{NP}^O$ on the support of $\mathcal D$
-- statement:
--   For every oracle $O=(A,B,C)$ in the support of $\mathcal D$,
--   $$\mathsf P^O=\mathsf{NP}^O.$$
--
--   The component $C$ answers every $\mathsf{NP}$-type machine at a level polynomial in its running time, so a polynomial-time machine can read off the answer.
--
--   Differences from the source:
--   - reading: any oracle in the support of D → every outcome of the sampling map on every seed; reason: at least as strong as the topological support
--   - reading: machines of S_t syntactically restricted to query levels up to ⌊√t⌋ and to the time and space bounds → every pair of code length below t, run with the truncated oracle and clocks; reason: makes the recursion well-founded; same value on machines obeying the restrictions
--   - encoding: a nondeterministic Turing machine in S^NP_t → a deterministic verifier reading a witness of length at most t; reason: the standard equivalent form, needed to give machines bit-string codes
--   - encoding: classical oracles, Turing machines, the universal gate set → `Oracle = Str → Bool`, the finite-table machines `OTM`, Clifford+T with an XOR oracle gate; reason: an explicit model of the paper's §3.2 conventions; same classes
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, Lemma 4.2, p. 22 (PDF p. 24)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_sampleABC
import Definitions.Def_QAdvFew_PoQOracle_P
import Definitions.Def_QAdvFew_PoQOracle_NP

namespace QAdvFew.PoQOracle

/-- **Lemma 4.2** (Goldin, Lombardi, Morimae, *Quantum Advantage has Few Complexity Implications*,
arXiv:2611.05303v1, Lemma 4.2, p. 22 (PDF p. 24)). Let `O = (A, B, C)` be any oracle in the support
of `D`; then `P^O = NP^O`.

**Formalization Note** "Any oracle in the support of `D`" is every outcome `sampleO ⊤ ω` of the
sampling map, for every seed `ω` (so for every family `F`). -/
theorem lemma_4_2 (ω : Seed) : P (sampleO ⊤ ω) = NP (sampleO ⊤ ω) := by sorry

end QAdvFew.PoQOracle
