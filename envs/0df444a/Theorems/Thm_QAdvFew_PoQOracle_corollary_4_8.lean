-- Prove2me | Theorems.Thm_QAdvFew_PoQOracle_corollary_4_8
-- name    : QAdvFew.PoQOracle.corollary_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:55:42.166817+00:00
-- url     : https://prove2.me/theorems/645aa762-82b3-4232-9310-325149237166
-- title:
--   Corollary 4.8 — $\mathsf{AC}^0[\oplus]$ circuits over the random oracle
-- statement:
--   Fix $t,d\in\mathbb N$ and let $t'\le t^{2^d}$. For each $(M,x)\in S^{\mathsf{NP}}_{t'}$ there is an $\mathsf{AC}^0[\oplus](2^{1+t^{2^d}},2d+2)$ circuit that takes as input $x$, $(\mathrm{RO}_1,\dots,\mathrm{RO}_{t^{2^{d-1}}})$, $(B_1,\dots,B_{t^{2^{d-1}}})$, $(C_1,\dots,C_t)$ and outputs $M^O(x)$ for all choices of oracle $O$ in the support of $\mathcal D$.
--
--   Each bit of a multilinear extension is a parity of oracle positions, so the $A$ inputs of Lemma 4.7 can be replaced by the random oracle at the cost of parity gates. The hardness of salted majority is then a statement about circuits over $\mathrm{RO}$.
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
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, Corollary 4.8, p. 24 (PDF p. 26)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_sampleABC
import Definitions.Def_QAdvFew_PoQOracle_truncO
import Definitions.Def_QAdvFew_PoQOracle_roInput
import Definitions.Def_QAdvFew_PoQOracle_IsAC0Xor

namespace QAdvFew.PoQOracle

open Classical in
/-- **Corollary 4.8** (Goldin, Lombardi, Morimae, *Quantum Advantage has Few Complexity
Implications*, arXiv:2611.05303v1, Corollary 4.8, p. 24 (PDF p. 26)). Fix `t, d ∈ ℕ` and let
`t' ≤ t^{2^d}`. For each `(M, x) ∈ S^NP_{t'}` there is an `AC0[⊕](2^{1+t^{2^d}}, 2d + 2)` circuit that
takes as input `x`, `(RO_1, …, RO_{t^{2^{d−1}}})`, `(B_1, …, B_{t^{2^{d−1}}})`, `(C_1, …, C_t)` and outputs
`M^O(x)` for all oracles `O` in the support of `D`.

**Formalization Note** As in `lemma_4_7`, with the random oracle `RO` (levels `≤ t^{2^{d−1}}`, input
`s` carrying `RO_{|s|}(s)`) in place of `A`; stated for every outcome of `D` and of every `D^(n)`.
The exponents are those of the rendered page (`t^{2^d}`, and `t^{2^{d−1}}`, the square root of
`t^{2^d}`), which the text layer flattens to `t2d`. At `d = 0` the index `t^{2^{−1}}` is read as `t`
(natural-number subtraction `d − 1 = 0`); there `t' ≤ t`, and the claim holds with the input
`C_{t'}(M, x)` itself.
NOT gates are not counted in the depth (`Circuit.depth`): counted, they make the statement false at
`d = 1`, since the parity of two free oracle bits has no depth-`2` circuit. -/
theorem corollary_4_8 (cut : ℕ∞) (t d t' : ℕ) (ht' : t' ≤ t ^ (2 ^ d)) (V : OTM) (x : List Bool)
    (hVx : (codePair V x).length < t') :
    ∃ C : Circuit (Fin x.length ⊕ List Bool ⊕ List Bool ⊕ List Bool),
      IsAC0Xor C ((2 : ℝ) ^ (1 + t ^ (2 ^ d))) (2 * d + 2) ∧
      ∀ ω : Seed,
        C.eval1 (fun _ => false)
            (Sum.elim (fun i => x.get i)
              (Sum.elim (roInput ω.1 ((t ^ (2 ^ (d - 1)) : ℕ) : ℕ∞))
                (Sum.elim (truncLevels (t ^ (2 ^ (d - 1))) (sampleABC cut ω).2.1)
                  (truncLevels t (sampleABC cut ω).2.2)))) =
          decide (npAccepts V (truncO (Nat.sqrt t') (sampleABC cut ω)) x t') := by sorry

end QAdvFew.PoQOracle
