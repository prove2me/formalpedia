-- Prove2me | Theorems.Thm_ParityDegreeDepth_Core_theorem_1_3_public
-- name    : ParityDegreeDepth.Core.theorem_1_3_public
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T04:18:57.730976+00:00
-- url     : https://prove2.me/theorems/480f37fa-ed74-583d-9cd5-7ebd87f7ad70
-- title:
--   Theorem 1.3 (public restatement): $D_\oplus(f)\le 1+\frac{2^{2d-1}-5}{3}\log_2\|\widehat f\|_1$
-- statement:
--   This is Theorem 1.3 of the source, stated over the public definitions of `ParityDegreeDepth_Core_Setting` (which reproduce verbatim the private context of the mission statement `ParityDegreeDepth.Main.theorem_1_3`).
--
--   Let $p:\mathbb F_2^n\to\mathbb F_2$ have ANF degree exactly $d\ge2$, let $f=(-1)^p$ and $F(x,y)=f(x+y)$. Then
--
--   $$
--   D_\oplus(f)\;\le\;1+\frac{2^{2d-1}-5}{3}\log_2\|\widehat f\|_1\;\le\;1+\frac{2^{2d-1}-5}{6}\log_2 s(f),
--   $$
--
--   $$
--   \tfrac12D^{\rm cc}(F)\le1+\frac{2^{2d-1}-5}{6}\log_2 s(f),\qquad D^{\rm cc}(F)\le2D_\oplus(f),
--   $$
--
--   and there is an absolute constant $C>0$ (uniform in $n$ and $d$) with
--
--   $$
--   D_\oplus(f)\le C\,4^d\log_2 s(f),\qquad \tfrac12D^{\rm cc}(F)\le C\,4^d\log_2 s(f).
--   $$
--
--   For $d=2$ the leading coefficient is $1$, i.e. $D_\oplus(f)\le1+\log_2\|\widehat f\|_1$, which is optimal for quadratic phases. The restriction $d\ge2$ is necessary: a nonconstant affine phase has $s(f)=1$ but depth one.
--
--   **Formalization Note** The mission statement declares the tree type as a `private inductive`, which makes it impossible for any separately compiled proof to match its type; this public restatement is otherwise identical.
-- source:
--   Zhang, Parity Decision Trees of Depth O(4^d log ||f^||_1) for Boolean Functions f of F2-Degree d, STOC 2027 submission #798, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/798.pdf, Theorem 1.3 (PDF p. 3, printed p. 2), with eq. (2) (D^cc(F) <= 2 D_xor(f)) and eq. (3)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BooleanFourier
import Definitions.Def_ParityCubes_anfCoeff
import Definitions.Def_DetCCHard_Protocol
import Definitions.Def_ParityDegreeDepth_Core_Setting

open scoped BigOperators
open ParityDegreeDepth.Core.Setting

theorem ParityDegreeDepth.Core.theorem_1_3_public :
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
