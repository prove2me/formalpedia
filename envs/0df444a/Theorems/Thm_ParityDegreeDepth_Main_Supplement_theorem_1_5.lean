-- Prove2me | Theorems.Thm_ParityDegreeDepth_Main_Supplement_theorem_1_5
-- name    : ParityDegreeDepth.Main.Supplement.theorem_1_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:49:54.80836+00:00
-- url     : https://prove2.me/theorems/9deb4d56-8957-451a-a097-ed7824f7706d
-- title:
--   Theorem 1.5 — parity decision tree depth bounded by $\log_2 W(f)$
-- statement:
--   Let $p:\mathbb F_2^n\to\mathbb F_2$ have algebraic-normal-form degree exactly $d\ge2$, and let $f=(-1)^p$ be its Boolean phase. Write $D_\oplus(f)$ for the least depth of a parity decision tree computing $f$ exactly (each internal node queries a nonzero parity $\langle a,x\rangle$), and $W(f)$ for the threshold weight of $f$: the least spectral norm $\|\widehat g\|_1$ of a real function $g$ with $f(x)g(x)\ge1$ for all $x$. Then
--
--   $$
--   D_\oplus(f)\le 1+\frac{2^{2d-1}-5}{3}\,\log_2 W(f).
--   $$
--
--   The statement holds for every $n$ and every $d\ge2$, with exactly this coefficient. Since $W(f)\le\|\widehat f\|_1$ (take $g=f$), it strengthens the first inequality of the mission's main theorem, Theorem 1.3, which has $\|\widehat f\|_1$ in place of $W(f)$.
--
--   **Formalization Note** $D_\oplus$, the degree and $\log_2$ are those of the mission's published operational context; $W$ is the infimum of witness spectral norms, which is at least $1$, so the logarithm is evaluated on a positive argument.
--
--   Differences from the source:
--   - encoding: D⊕(f) → parityDepth (phase p), the least depth of an exact parity decision tree in the published Context; reason: the same quantity
--   - encoding: W(f) defined as a minimum → the real infimum of the same set of witness spectral norms; reason: the minimum is attained (paper's remark after Definition C.1), so the values agree
--   - encoding: p of degree exactly d ≥ 2 → anfDegree p = d in WithBot ℕ, d : ℕ with 2 ≤ d, exponent 2*d − 1 in ℕ; reason: the natural-number subtraction is exact because d ≥ 2
--   - encoding: log₂ → logTwo x = Real.log x / Real.log 2; reason: the argument W(f) ≥ 1 is positive, so this is the base-two logarithm
-- source:
--   Shengyu Zhang, STOC 2027 submission #798 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/798.pdf, SHA-256 02e6bad861054e233c6877aa352d0014cf84172cde536433dd6e24588277680b, Theorem 1.5, PDF p. 4 (printed p. 3); hypotheses of Theorem 1.3, PDF p. 3 (printed p. 2); proof §C.1, PDF p. 26 (printed p. 25).

import Mathlib
import Definitions.Def_ParityDegreeDepth_Main_Context
import Definitions.Def_ParityDegreeDepth_Main_Supplement_ThresholdWeight

open scoped BigOperators
noncomputable section

namespace ParityDegreeDepth.Main.Supplement

open ParityDegreeDepth.Main

/-- Zhang, STOC 2027 submission #798, Theorem 1.5, PDF p. 4 (printed p. 3); proof §C.1,
PDF p. 26 (printed p. 25). SHA-256
02e6bad861054e233c6877aa352d0014cf84172cde536433dd6e24588277680b.
Under the hypotheses of Theorem 1.3 (exact ANF degree `d ≥ 2`, `f = (-1)^p`, every `n`),
`D⊕(f) ≤ 1 + ((2^(2d-1) - 5)/3) log₂ W(f)`. -/
theorem theorem_1_5 (n d : ℕ) (p : Vec n (ZMod 2) → ZMod 2)
    (hd : 2 ≤ d) (hp : anfDegree p = (d : WithBot ℕ)) :
    (parityDepth (phase p) : ℝ) ≤
      1 + ((2 : ℝ) ^ (2 * d - 1) - 5) / 3 * logTwo (thresholdWeight (phase p)) := by sorry

end ParityDegreeDepth.Main.Supplement
