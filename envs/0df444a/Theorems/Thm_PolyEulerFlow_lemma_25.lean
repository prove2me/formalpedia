-- Prove2me | Theorems.Thm_PolyEulerFlow_lemma_25
-- name    : PolyEulerFlow.lemma_25
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:20:09.291673+00:00
-- url     : https://prove2.me/theorems/2d592045-2326-4271-b660-0197428f856b
-- title:
--   Lemma 25 — cumulative gain of the stack normal form
-- statement:
--   There is a fixed constant $G>0$ such that, for every program in the dyadic two-stack normal form, every input $x$, every scale $h=2^{-s}$ and every subinterval $k_1<k_2$ of its computation along which the configurations are valid (stack heights at most $H_s=\lfloor(s-2)/2\rfloor$, pops only on nonempty stacks), the linear parts $D_{\sigma_k}$ of the selected transitions satisfy
--   $$\|D_{\sigma_{k_2-1}}\cdots D_{\sigma_{k_1}}\|_\infty\le\frac{G}{h}.$$
--   The same bound holds after the resetting halt, where the linear part is zero.
--
--   This is the interval gain bound (4) for the stack normal form: products of transitions grow by at most a factor $1/h$, however long the computation.
--
--   Differences from the source:
--   - generalization: a fixed constant G for the stack normal form of the fixed source machine → one G for every program in the normal form; reason: the proof (p.56) gives G = 3 for all of them; a constant per program is a special case
--   - generalization: along every valid source computation → validity required only at the configurations where the transitions of the interval are taken, and only heights and pops; reason: a valid computation satisfies these conditions
--   - encoding: the matrices D_σ of the normal form → the block-diagonal linear part: 1/4, 4, 1, 0 per stack, (1, −b; 0, 1/2), I, 0 on the reader, 0 on control bits and on halting transitions; reason: pp.55–56 and §6.2
-- source:
--   Bournez, One Polynomial Field for Every Euler Step and the Flow (manuscript, sha256 c4e01b2b…), Lemma 25, p.26 (PDF 28); linear parts from the proof, pp.55–56 (PDF 57–58)

import Mathlib
import Definitions.Def_PolyEulerFlow_DyadicProgram
import Definitions.Def_PolyEulerFlow_SeparatedAffineProgram

namespace PolyEulerFlow

/-- **Lemma 25 (Cumulative gain)**, p.26 (PDF 28). Bournez, One Polynomial Field for Every Euler Step and the Flow (manuscript,
sha256 c4e01b2b…).

There is a fixed constant `G` such that, along every valid computation of a program in the dyadic two-stack normal form at scale `h = 2^{-s}`
and for every subinterval of transitions `k₁ < k₂`, the product of the linear parts of the selected transitions satisfies
`‖D_{σ_{k₂-1}} ⋯ D_{σ_{k₁}}‖∞ ≤ G/h`; the same bound holds after the resetting halt.

**Formalization Note** The linear part of a transition is block diagonal: `1/4` for a push, `4` for a pop, `1` for no operation, `0` for a reset on each
stack; `(1, -b; 0, 1/2)`, `I` or `0` on the reader; `0` on the control bits; and `0` for a halting transition or a halted configuration (the constant
branch). Validity of a configuration is heights at most `H_s = ⌊(s - 2)/2⌋` and pops only on nonempty stacks (p.24); it is required at the
configurations where the transitions of the interval are taken (`k₁ ≤ k < k₂`). `G` is uniform over all programs of the normal form (the proof, p.56, gives `G = 3`), which contains the
statement for each fixed program. -/
theorem lemma_25 :
    ∃ G : ℝ, 0 < G ∧
      ∀ (P : DyadicProgram) (x s k1 k2 : ℕ), k1 < k2 →
        (∀ k, k1 ≤ k → k < k2 → P.IsValidConfig s (P.conf x (scale s) k)) →
        matInfNorm (intervalProd (fun k => P.linearPart (scale s) (P.conf x (scale s) k)) k1 (k2 - k1))
          ≤ G / scale s := by sorry

end PolyEulerFlow
