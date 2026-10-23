-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P75_bisectionTests
-- name    : QAlgorithms.Papers.Independent.Information100.P75.bisectionTests
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T13:17:06.551733+00:00
-- url     : https://prove2.me/theorems/9d752f73-faf9-4b3b-a398-350dfc329ee7
-- title:
--   Exact width threshold tests and bisection intervals
-- statement:
--   For a square complex matrix $X$, $W(X)$ denotes its numerical range, equivalently the values $\operatorname{Tr}(\sigma X)$ over PSD matrices $\sigma$ of trace one. Put $\Gamma_X=\{\theta\in[-\pi,\pi):\operatorname{Re}(e^{i\theta}X)\succeq0\}$, where $\operatorname{Re}Y=(Y+Y^\dagger)/2$, with Lebesgue length $|\Gamma_X|$ in radians. The ordinary width is $\operatorname{sw}(X)=\pi$ when $0\in W(X)$ and $\pi-|\Gamma_X|$ otherwise. For a complex subspace $\mathcal M$, $\operatorname{sw}^*(\mathcal M)=\inf_{X\in\mathcal M}\operatorname{sw}(X)$. The overlined width of a nonzero matrix is $\overline{\operatorname{sw}}(X)=\pi-|\Gamma_X|$.
--
--   Let $n\ge1$, let $(A_l)_{l=1}^k$ be a basis of a complex subspace $\mathcal A\subset M_n(\mathbb C)$, and let $0\le\alpha<\pi$. Then
--
--   $$D_\alpha(A_1,\ldots,A_k)=0\iff\operatorname{sw}^*(\mathcal A)\ge\pi-\alpha,\qquad D_\alpha(A_1,\ldots,A_k)>0\iff\operatorname{sw}^*(\mathcal A)<\pi-\alpha.$$
--
--   Start with $[L_0,U_0]=[0,\pi]$. At midpoint $m$, test $D_{\pi-m}$: zero keeps $[m,U]$, and a positive value keeps $[L,m]$. After $t$ steps,
--
--   $$L_t\le\operatorname{sw}^*(\mathcal A)\le U_t,\qquad U_t-L_t=\pi/2^t.$$
--
--   For every $\varepsilon>0$ some such interval has length less than $\varepsilon$. These are ideal exact-value tests; they assert no numerical tolerance or computational cost.
-- source:
--   Parallel quantum channel discrimination and numerical ranges in tensor product subspaces, arXiv:2609.20781v1, PDF p. 4, Section 3, bisection tests

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P75

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P75

open Classical

open scoped ComplexConjugate ComplexOrder Matrix

open MeasureTheory

/-- Section 3 bisection, PDF p.4: both exact threshold tests, certified bisection
intervals and arbitrary precision. This asserts no floating-point zero test or runtime. -/
theorem bisectionTests {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : Submodule ℂ (Mat ι)) {k : ℕ} (b : Module.Basis (Fin k) ℂ M)
    (a : ℝ) (ha : 0 ≤ a) (hap : a < Real.pi) :
    let X := fun j => (b j : Mat ι)
    (sdpValue a X = 0 ↔ Real.pi - a ≤ infWidth M) ∧
    (0 < sdpValue a X ↔ infWidth M < Real.pi - a) ∧
    (∀ t : ℕ, (bisect X t).1 ≤ infWidth M ∧ infWidth M ≤ (bisect X t).2 ∧
      (bisect X t).2 - (bisect X t).1 = Real.pi / (2 : ℝ) ^ t) ∧
    (∀ e : ℝ, 0 < e → ∃ t : ℕ, (bisect X t).2 - (bisect X t).1 < e) := by sorry

end QAlgorithms.Papers.Independent.Information100.P75

end
