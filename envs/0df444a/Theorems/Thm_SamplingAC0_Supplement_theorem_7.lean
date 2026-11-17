-- Prove2me | Theorems.Thm_SamplingAC0_Supplement_theorem_7
-- name    : SamplingAC0.Supplement.theorem_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:42:30.988441+00:00
-- url     : https://prove2.me/theorems/6fc994af-4fe8-4d4e-aac1-a32a2fe5022f
-- title:
--   Theorem 7 (Exact symmetric sampling) — AC$^0$ samples $(U,f(U))$ exactly, constructed in polynomial time
-- statement:
--   There are absolute constants $c_1,c_2>0$ and an algorithm $A$, mapping binary strings to binary strings in deterministic polynomial time, with the following property. For every $n\ge0$ and every symmetric function $f:\{0,1\}^n\to\{0,1\}$, given by its values $v(0),\dots,v(n)$ on the Hamming weights, $A(v(0)\cdots v(n))$ is the description of an AC$^0$ sampler $C$ with
--
--   1. at most $n^{c_1}$ wires,
--   2. depth at most $c_2$, and
--   3. output distribution exactly $(U,f(U))$: for $x$ uniform on $\{0,1\}^n$, the string $(x_1,\dots,x_n,f(x))$ has the same distribution as $C$'s output.
--
--   The constants and the algorithm do not depend on $n$ or $f$.
--
--   Earlier AC$^0$ samplers for $(U,f(U))$, for instance with $f$ the majority function, had an exponentially small error; this sampler has none.
--
--   **Formalization Note** An AC$^0$ sampler has one circuit of unbounded fan-in AND/OR gates per output bit, and its number $m$ of input bits is free. "Constructed efficiently" is computability of $v\mapsto$ (description of $C$) by a polynomial-time Turing machine on binary strings. For $n=0,1$ the outputs are literals or constants, which need no wires, so the bound $n^{c_1}$ is meaningful for every $n$.
--
--   Differences from the source:
--   - encoding: one AC$^0$ circuit with $n+1$ outputs → one circuit per output bit, wires summed and depth maximised; reason: a shared circuit with $W$ wires gives per-output circuits with at most $(n+1)W$ wires and the same depth, and conversely, so bounds $n^c$ and $c$ mean the same
--   - encoding: "constructed efficiently given the $n+1$ values" → a polynomial-time function on binary strings mapping the value table to the sampler's description (unary indices); reason: the description is injective and polynomially equivalent to a binary-index description for polynomial-size circuits
-- source:
--   Riazanov–Viola, Sampling Tools and the Power of AC0, STOC 2027 submission (manuscript sha256 99c33d30…), Theorem 7, p.4 (proof §4, pp.13–14)

import Mathlib
import Definitions.Def_DDNNFNeg_Supplement_PolyTimeFun
import Definitions.Def_SamplingAC0_Supplement_ACSampler
import Definitions.Def_SamplingAC0_Supplement_symTarget
import Definitions.Def_SamplingAC0_Supplement_encodeSampler
set_option autoImplicit false

namespace SamplingAC0.Supplement

/-- **Theorem 7 (Exact symmetric sampling).** Riazanov–Viola, *Sampling Tools and the Power of
AC0*, STOC 2027 submission (manuscript sha256 99c33d30…), Theorem 7, p.4 (proof §4, pp.13–14):
"For every symmetric function f : {0, 1}^n → {0, 1}, there is an AC0 circuit of n^c wires and depth
c whose output distribution is exactly (U, f(U)). The circuit can be constructed efficiently given
the n + 1 values of f on the possible Hamming weights."

**Formalization Note.**
* c-notation (p.2): `c₁` (in `n^{c₁}` wires) and `c₂` (depth) are absolute positive constants,
  chosen before the construction algorithm `A`, `n` and `f`.
* A symmetric `f` is given by its value table `v : {0,…,n} → {0,1}` (`f x = v(|x|)`), with no
  restriction on `v`. "Exactly" is equality of distributions on `{0,1}^{n+1}`, coordinates ordered
  `(x₁, …, xₙ, f(x))` (`symTarget`).
* The circuit is an `ACSampler` (one published `MantriCVQ.ACCircuit` per output bit, wires and depth
  as defined there; the number `m` of input bits is free).
* "Constructed efficiently": a single function `A` on binary strings, computable in polynomial time
  (published `DDNNFNeg.Supplement.PolyTimeFun`, Mathlib's `TM2ComputableInPolyTime`), maps the
  table `v` (written `v(0), …, v(n)`) to the code `encodeSampler C` of a circuit `C` with all the
  properties above.
* The statement is for every `n`, including `n = 0, 1`, where literal and constant outputs need no
  wires. -/
theorem theorem_7 :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∃ A : List Bool → List Bool, DDNNFNeg.Supplement.PolyTimeFun A ∧
        ∀ (n : ℕ) (v : Fin (n + 1) → Bool), ∃ C : ACSampler (n + 1),
          A (List.ofFn v) = encodeSampler C ∧
          (C.wires : ℝ) ≤ (n : ℝ) ^ c₁ ∧ (C.depth : ℝ) ≤ c₂ ∧
          C.dist = symTarget n v := by sorry

end SamplingAC0.Supplement
