-- Prove2me | Theorems.Thm_SliceLinearity_Tests_proposition_5_2
-- name    : SliceLinearity.Tests.proposition_5_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T02:39:30.628461+00:00
-- url     : https://prove2.me/theorems/8b7a94c4-d07e-4e85-92e0-2904aa6924ae
-- title:
--   Proposition 5.2 — multilinear estimate for the active-set test, for unbounded complex functions
-- statement:
--   Fix $0<p<1$. Sample $x,y_1,\dots,y_m$ as in the active-set test ($m=\lceil1/p_*\rceil$). For arbitrary complex functions $f,h_1,\dots,h_m$ on $\mathbb F_2^n$,
--   $$\Big|\mathbb E\Big[f(x)\prod_{j=1}^mh_j(y_j)\Big]\Big|\le\max_\chi|\langle f,\chi\rangle_{\mu_p}|\cdot\prod_{j=1}^m\|h_j\|_{2,\mu_p}.$$
--
--   Differences from the source:
--   - encoding: the joint law of x, y₁, …, y_m in the active-set test → λ^{⊗n} with λ = activeSetTestLaw p, query 0 = x and query j.succ = y_{j+1}; reason: the columns of the test are i.i.d. with this law; same distribution
-- source:
--   Aydin, Larsen, Mittal, Richelson, Roy, Low Soundness Linearity Testing on Subsets of the Hypercube, STOC 2027 submission (manuscript sha256 457be236…), §5.1, p. 30 (PDF 32), Proposition 5.2

import Mathlib
import Definitions.Def_SliceLinearity_Tests_BiasedAnalysis
import Definitions.Def_SliceLinearity_Tests_ActiveSet

set_option autoImplicit false

namespace SliceLinearity.Tests

/-- **Proposition 5.2** (A multilinear estimate for the active-set test), p. 30 (PDF 32). Fix
`0 < p < 1` and sample `x, y₁, …, y_m` as in the active-set test (`m = ⌈1/p*⌉`; query `0` is `x`, query
`j.succ` is `y_{j+1}`). For arbitrary complex functions `f, h₁, …, h_m` on `F₂ⁿ`,
`|E[f(x) ∏_j h_j(y_j)]| ≤ max_χ |⟨f, χ⟩_{μ_p}| · ∏_j ‖h_j‖_{2,μ_p}`. -/
theorem proposition_5_2 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) {n : ℕ} (f : Cube n → ℂ)
    (h : Fin (activeM p) → Cube n → ℂ) :
    ‖∑ z : Fin (activeM p + 1) → Cube n,
        (tensorPow (activeSetTestLaw p) n z : ℂ) * (f (z 0) * ∏ j, h j (z j.succ))‖ ≤
      maxCorr (muP p) f * ∏ j, norm2W (muP p) (h j) := by sorry

end SliceLinearity.Tests
