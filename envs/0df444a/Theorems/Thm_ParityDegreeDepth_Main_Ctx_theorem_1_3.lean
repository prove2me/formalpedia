-- Prove2me | Theorems.Thm_ParityDegreeDepth_Main_Ctx_theorem_1_3
-- name    : ParityDegreeDepth.Main.Ctx.theorem_1_3
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T05:17:28.356341+00:00
-- url     : https://prove2.me/theorems/336db83d-ed65-5c0f-aec2-49167ef456b2
-- title:
--   Theorem 1.3 over the public context: $D_\oplus(f)\le 1+\frac{2^{2d-1}-5}{3}\log_2\|\hat f\|_1$
-- statement:
--   There is an absolute constant $C>0$, independent of $n$, $d$, and $p$, such that every phase $f=(-1)^p$ of exact algebraic normal-form degree $d\ge2$ on $\mathbb F_2^n$ satisfies the complete chain
--   $$D_\oplus(f)\le1+\frac{2^{2d-1}-5}{3}\log_2\|\widehat f\|_1\le1+\frac{2^{2d-1}-5}{6}\log_2s(f).$$
--   For the XOR function $F(x,y)=f(x+y)$ one also has
--   $$\tfrac12D^{\rm cc}(F)\le1+\frac{2^{2d-1}-5}{6}\log_2s(f),\qquad D^{\rm cc}(F)\le2D_\oplus(f),$$
--   and the dimension- and degree-uniform consequences
--   $$D_\oplus(f)\le C4^d\log_2s(f),\qquad\tfrac12D^{\rm cc}(F)\le C4^d\log_2s(f).$$
--   Both depths minimize the worst-case costs of actual finite exact computing trees or deterministic public-output binary protocols. The same middle expression appears in the two comparisons.
--
--   This is the paper's main explicit spectral-norm and sparsity bound, including its concluding communication consequence.
--
--   **Formalization Note.** This is the mission goal (Theorem 1.3) with the identical Lean statement, but stated over the public shared context `Def_ParityDegreeDepth_Main_Context` (the same definitions used by the paper's Supplement items) instead of private in-file copies. A private `inductive ParityTree` in a statement can never be matched by the verifier, because a separately compiled solution cannot refer to another module's private inductive. Over the public context the statement is checkable.
-- source:
--   Shengyu Zhang, STOC 2027 submission #798 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/798.pdf, Theorem 1.3, PDF page 3 / printed page 2 Eq. (2), PDF 2 / printed 1.

import Mathlib
import Definitions.Def_ParityDegreeDepth_Main_Context

open scoped BigOperators
noncomputable section

namespace ParityDegreeDepth.Main.Ctx

open ParityDegreeDepth.Main

/-- Theorem 1.3 of Zhang, STOC 2027 submission #798, stated over the public shared context
`Def_ParityDegreeDepth_Main_Context`. -/
theorem theorem_1_3:
    ∃ C : ℝ, 0 < C ∧ ∀ (n d : ℕ) (p : Vec n (ZMod 2) → ZMod 2),
    2 ≤ d → anfDegree p = (d : WithBot ℕ) →
    (parityDepth (phase p) : ℝ) ≤
      1 + ((2 : ℝ) ^ (2 * d - 1) - 5) / 3 * logTwo (spectralNorm (phase p)) ∧
    1 + ((2 : ℝ) ^ (2 * d - 1) - 5) / 3 * logTwo (spectralNorm (phase p)) ≤
      1 + ((2 : ℝ) ^ (2 * d - 1) - 5) / 6 * logTwo (sparsity (phase p)) ∧
    (communicationDepth (phase p) : ℝ) / 2 ≤
      1 + ((2 : ℝ) ^ (2 * d - 1) - 5) / 6 * logTwo (sparsity (phase p)) ∧
    communicationDepth (phase p) ≤ 2 * parityDepth (phase p) ∧
    (parityDepth (phase p) : ℝ) ≤ C * (4 : ℝ) ^ d * logTwo (sparsity (phase p)) ∧
    (communicationDepth (phase p) : ℝ) / 2 ≤ C * (4 : ℝ) ^ d * logTwo (sparsity (phase p)) := by sorry

end ParityDegreeDepth.Main.Ctx
