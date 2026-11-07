-- Prove2me | Theorems.Thm_QAdvFew_PoQOracle_lemma_4_7
-- name    : QAdvFew.PoQOracle.lemma_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:55:56.83925+00:00
-- url     : https://prove2.me/theorems/3000fd2b-1708-4391-9419-7aabb9cdae14
-- title:
--   Lemma 4.7 — oracle Turing machines as $\mathsf{AC}^0$ circuits
-- statement:
--   Fix $t,d\in\mathbb N$ and let $t'\le t^{2^d}$. For each $(M,x)\in S^{\mathsf{NP}}_{t'}$ there is an $\mathsf{AC}^0(2^{1+t^{2^d}},2d)$ circuit that takes as input $x$, $(A_1,\dots,A_{t^{2^{d-1}}})$, $(B_1,\dots,B_{t^{2^{d-1}}})$, $(C_1,\dots,C_t)$ and outputs $M^O(x)$ for all choices of oracle $O=(A,B,C)$ in the support of $\mathcal D$.
--
--   This converts machines into small constant-depth circuits in the oracle's truth tables, which is what the $\mathsf{AC}^0$ bound of Lemma 3.10 can then be applied to. It is the argument of Lemma 35 of [AIK22].
--
--   **Formalization Note** The circuit's inputs are the bits of $x$ and the query-indexed truth tables of $A$, $B$ and $C$ at the listed levels, with other entries $0$.
--
--   Differences from the source:
--   - reading: depth: the largest number of gates on an input-to-output path, with NOT among the gates (Definition 3.9) → NOT gates are not counted in the depth; reason: the usual AC0 convention; counting them makes this statement false at d = 1, since the parity of two free oracle bits has no depth-2 circuit with counted NOT gates
--   - reading: circuit size → the length of the circuit's explicit binary description, an input named by a string s costing about 2|s| bits; reason: §3.2.1, p. 12; the printed bound is kept
--   - reading: t^{2^{d−1}} at d = 0 → the index t (natural-number subtraction); reason: the printed index is not a number at d = 0; the inputs at those levels are not needed there, where the circuit is the single input C_{t'}(M, x)
--   - generalization: all oracles in the support of D → every outcome of D and of every D^(n), through the parameter cut; reason: the paper notes on p. 24 that the proof applies to D^(n), and Theorem 4.12 uses it; cut = ⊤ is the printed statement
--   - reading: any oracle in the support of D → every outcome of the sampling map on every seed; reason: at least as strong as the topological support
--   - reading: machines of S_t syntactically restricted to query levels up to ⌊√t⌋ and to the time and space bounds → every pair of code length below t, run with the truncated oracle and clocks; reason: makes the recursion well-founded; same value on machines obeying the restrictions
--   - encoding: a nondeterministic Turing machine in S^NP_t → a deterministic verifier reading a witness of length at most t; reason: the standard equivalent form, needed to give machines bit-string codes
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, Lemma 4.7, p. 24 (PDF p. 26)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_sampleABC
import Definitions.Def_QAdvFew_PoQOracle_truncO
import Definitions.Def_QAdvFew_PoQOracle_IsAC0

namespace QAdvFew.PoQOracle

open Classical in
/-- **Lemma 4.7 (Representing oracle Turing machines as AC0 circuits)** (Goldin, Lombardi, Morimae,
*Quantum Advantage has Few Complexity Implications*, arXiv:2611.05303v1, Lemma 4.7, p. 24
(PDF p. 26); Lemma 35 of [AIK22]). Fix `t, d ∈ ℕ` and let `t' ≤ t^{2^d}`. For each
`(M, x) ∈ S^NP_{t'}` there is an `AC0(2^{1+t^{2^d}}, 2d)` circuit that takes as input `x`,
`(A_1, …, A_{t^{2^{d−1}}})`, `(B_1, …, B_{t^{2^{d−1}}})`, `(C_1, …, C_t)` and outputs `M^O(x)` for all
oracles `O = (A, B, C)` in the support of `D`.

**Formalization Note** The nondeterministic machine `M` is a verifier `V` (`npAccepts`), and
`(V, x) ∈ S^NP_{t'}` is `|codePair V x| < t'`; `M^O(x)` is its acceptance with the oracle truncated
to levels `≤ ⌊√t'⌋` (the value `C_{t'}(M, x)`). The circuit's inputs are the bits of `x` and the
query-indexed truth tables of `A`, `B` (levels `≤ t^{2^{d−1}}`) and `C` (levels `≤ t`), other entries
`0`. The statement is made for every outcome of the sampling map of `D` and of every `D^(n)` (`cut`),
as the paper notes before Lemma 4.9 (p. 24). Size is description length.
The exponents are those of the rendered page (`t^{2^d}`, and `t^{2^{d−1}}`, the square root of
`t^{2^d}`), which the text layer flattens to `t2d`. At `d = 0` the index `t^{2^{−1}}` is read as `t`
(natural-number subtraction `d − 1 = 0`); there `t' ≤ t`, and the claim holds with the input
`C_{t'}(M, x)` itself.
NOT gates are not counted in the depth (`Circuit.depth`): counted, they make the statement false at
`d = 1`, since the parity of two free oracle bits has no depth-`2` circuit. -/
theorem lemma_4_7 (cut : ℕ∞) (t d t' : ℕ) (ht' : t' ≤ t ^ (2 ^ d)) (V : OTM) (x : List Bool)
    (hVx : (codePair V x).length < t') :
    ∃ C : Circuit (Fin x.length ⊕ List Bool ⊕ List Bool ⊕ List Bool),
      IsAC0 C ((2 : ℝ) ^ (1 + t ^ (2 ^ d))) (2 * d) ∧
      ∀ ω : Seed,
        C.eval1 (fun _ => false)
            (Sum.elim (fun i => x.get i)
              (Sum.elim (truncLevels (t ^ (2 ^ (d - 1))) (sampleABC cut ω).1)
                (Sum.elim (truncLevels (t ^ (2 ^ (d - 1))) (sampleABC cut ω).2.1)
                  (truncLevels t (sampleABC cut ω).2.2)))) =
          decide (npAccepts V (truncO (Nat.sqrt t') (sampleABC cut ω)) x t') := by sorry

end QAdvFew.PoQOracle
