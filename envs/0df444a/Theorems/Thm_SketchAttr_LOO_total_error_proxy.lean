-- Prove2me | Theorems.Thm_SketchAttr_LOO_total_error_proxy
-- name    : SketchAttr.LOO.total_error_proxy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T15:29:22.592197+00:00
-- url     : https://prove2.me/theorems/f47abf24-ea0c-49e7-a954-5f9ab54e33ae
-- title:
--   Section 5.2, p. 17 — total error proxy bound
-- statement:
--   Let $f:\mathbb C^n\to\mathbb C$ be an $\alpha$-stable scalar arithmetic circuit real-valued on $[0,1]^n$ with $\alpha(4)<\infty$, and let $N\ge1$. For $v_{i,r}=\binom{2r-2}{r-1}\|T_f^{(r)}[e_i,\cdot]\|_F^2$ and $s_i=\sum_{r=2}^N\sqrt{v_{i,r}}$, the two finite-sum inequalities are
--   $$\left(\sum_{i=1}^n s_i^2\right)^{1/2}\le\sum_{r=2}^N\sqrt{\binom{2r-2}{r-1}}\|T_f^{(r)}\|_F\le\frac{\alpha(4)}4.$$
--   The rightmost value is the paper's evaluated geometric series $\alpha(4)\sum_{r=2}^\infty2^{r-1}/4^r$. This controls aggregate coordinate error without a bound that grows with $n$.
--
--   Differences from the source:
--   - encoding: the geometric series alpha(4) sum from r=2 to infinity of 2^(r-1)/4^r → the evaluated value alpha(4)/4; finite sums use Icc 2 N and the finite profile value uses toReal; reason: the series equals 1/4 and finiteness is explicit, so no bound or endpoint case changes
--   - encoding: positive integer input dimension n and indices in [n] → Fin n with an explicit hypothesis 1 <= n; reason: this records the positive-dimension convention in Section 3.1 and changes only the index base
-- source:
--   Liaw, Mehta, Velegkas, Zhou, Sketching Language Models for Context Attribution, STOC 2027 submission #9 (PDF sha256 86af2569e45c55b1009e7453d4f53047b5820d44868a7f528bdb6fed1a2ef0e2), p. 17, Section 5.2, Selecting Exact Evaluations, displayed total error proxy bound; canonical PDF: https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/9.pdf

import Mathlib
import Definitions.Def_SketchAttr_LOO_Stability
open scoped ENNReal

namespace SketchAttr.LOO

/-- Section 5.2, p.17, including both finite-sum inequalities. The last
geometric series has value alpha(4)/4. -/
theorem total_error_proxy (n : ℕ) (hn : 1 ≤ n) (c : Circuit n 1)
    (hreal : c.RealOnCube) (α : StabilityProfile)
    (hstable : IsStable (circuitFunction c) α) (hfinite : α ⟨4, by norm_num⟩ < ⊤)
    (N : ℕ) (hN : 1 ≤ N) :
    Real.sqrt (∑ i : Fin n, errorProxy (circuitFunction c) N i ^ 2) ≤
      (∑ r ∈ Finset.Icc 2 N,
        Real.sqrt (Nat.choose (2*r-2) (r-1) : ℝ) *
          frobNorm (taylorTensor (circuitFunction c) r)) ∧
    (∑ r ∈ Finset.Icc 2 N,
        Real.sqrt (Nat.choose (2*r-2) (r-1) : ℝ) *
          frobNorm (taylorTensor (circuitFunction c) r)) ≤
      (α ⟨4, by norm_num⟩).toReal / 4 := by sorry

end SketchAttr.LOO
