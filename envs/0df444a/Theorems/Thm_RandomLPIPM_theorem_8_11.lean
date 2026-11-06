-- Prove2me | Theorems.Thm_RandomLPIPM_theorem_8_11
-- name    : RandomLPIPM.theorem_8_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:10:20.1098+00:00
-- url     : https://prove2.me/theorems/48916fc4-0373-4fa9-a775-4ee6171d8df1
-- title:
--   Theorem 8.11 — the $d$ largest coordinates of $\hat x$ form the optimal basis and the basis system returns the optimum
-- statement:
--   Let $A\in\mathbb R^{d\times n}$ have independent $\mathcal N(0,1)$ entries, $1\le d<n$. For every $q>0$ and $n\ge3$, with probability at least $1-n^{-(q+1)}$ the following holds: for any $\hat\mu\in(0,n^{-2(q+4)}/2048]$ and any $\hat x$ strictly feasible for LP(A) with $E_{\hat\mu}(\hat x)\le1/6$, letting $\hat B$ be the indices of the $d$ largest coordinates of $\hat x$ and $\hat N=[n]\setminus\hat B$:
--   1. LP(A) has a unique optimal solution $(x^*,y^*,s^*)$;
--   2. $(\hat B,\hat N)=(B^*,N^*)$, where $B^*=\operatorname{supp}(x^*)$ and $N^*=\operatorname{supp}(s^*)$;
--   3. $(x^*,y^*,s^*)$ is the (unique) solution of
--   $$A_{\hat B}x_{\hat B}=A\mathbf 1,\quad x_{\hat N}=0,\quad A^\top y+s=\mathbf 1,\quad s_{\hat B}=0 .$$
--
--   This is the termination step of the paper's method: one linear solve after path following yields the exact optimum.
--
--   Differences from the source:
--   - reading: the optimal solution (x*, s*) is the solution of the basis system → the optimum (x*, y*, s*) is unique and the basis system has the unique solution (x*, y*, s*) (roundBasis returns it); reason: 'the solution' of the system; y is the dual vector of the system
--   - encoding: Section 8 setting (p.68) → hypotheses 1 ≤ d < n; reason: the section's standing assumption on A ∈ ℝ^{d×n}
--   - encoding: probability of the event → outer Gaussian measure of the failure set bounded by the failure probability; reason: no measurability assumption is needed; for a measurable event it is 1 − P(event)
--   - reading: the unsubscripted norm of E_μ (p.73) → the Euclidean norm; reason: Theorem 2.1 and Remark 1.2 write ‖·‖₂, and the proofs of Lemmas 9.5 and 9.7 use ℓ2
--   - encoding: the index set of the d largest coordinates of x̂ → topBasis, ties broken by index; roundBasis = (0, 0, 0) when the basis system has no unique solution; reason: the page leaves ties open; on the success event the two groups of coordinates are separated and the system has a unique solution
-- source:
--   Dadush–Jiang–Kyng–Ma, Interior Point Methods Solve Random LPs in polylog(n) iterations, STOC 2027 submission (manuscript sha256 a8a320f9…), Theorem 8.11, pp.73–74

import Mathlib
import Definitions.Def_GaussianMatrix_basic
import Definitions.Def_RandomLPIPM_IsPrimalStrictFeas
import Definitions.Def_RandomLPIPM_IsPDOptimal
import Definitions.Def_RandomLPIPM_proximity
import Definitions.Def_RandomLPIPM_topBasis
import Definitions.Def_RandomLPIPM_roundBasis

open Matrix MeasureTheory

namespace RandomLPIPM

/-- **Theorem 8.11 (basis identification for LP(A)).** Dadush–Jiang–Kyng–Ma, *Interior Point Methods Solve Random LPs in polylog(n) iterations*, STOC 2027 submission (manuscript sha256 a8a320f9…), Theorem 8.11, pp.73–74.

Let `A ∈ ℝ^{d×n}` have independent `N(0,1)` entries. For every `q > 0` and `n ≥ 3`, with probability
at least `1 − n^{−(q+1)}`: for any `μ̂ ∈ (0, n^{−2(q+4)}/2048]` and `x̂` strictly feasible to LP(A) with
`E_μ̂(x̂) ≤ 1/6`, letting `B̂` be the indices of the `d` largest coordinates of `x̂` and `N̂ = [n] ∖ B̂`,
`(B̂, N̂)` is the optimal basis of LP(A), i.e. `(B̂, N̂) = (B*, N*)`, and the optimal solution
`(x*, s*)` of LP(A) is the solution of `A_B̂ x_B̂ = A1`, `x_N̂ = 0`, `Aᵀy + s = 1`, `s_B̂ = 0`.

**Formalization Note.** Section 8 setting `1 ≤ d < n` (p.68). On the success event the optimal
solution `(x*, y*, s*)` exists and is unique, `B̂ = supp(x*)`, `N̂ = supp(s*)`, and the rounding
`roundBasis` (the unique solution of the basis system) returns `(x*, y*, s*)`. `μ̂ ≤ n^{−2(q+4)}/2048`
is `n` to the power `−2(q+4)`, divided by `2048`. -/
theorem theorem_8_11 (q : ℝ) (hq : 0 < q) (d n : ℕ) (hn : 3 ≤ n) (hd1 : 1 ≤ d) (hdn : d < n) :
    GaussianMatrix.gaussianMatrix d n {A | ¬ ∀ μh : ℝ, 0 < μh → μh ≤ (n : ℝ) ^ (-(2 * (q + 4))) / 2048 →
        ∀ xh : Fin n → ℝ, IsPrimalStrictFeas (Matrix.of A) (Matrix.of A *ᵥ 1) xh →
        proximity (Matrix.of A) (Matrix.of A *ᵥ 1) 1 μh xh ≤ 1 / 6 →
        ∃ (x : Fin n → ℝ) (y : Fin d → ℝ) (s : Fin n → ℝ),
          IsPDOptimal (Matrix.of A) (Matrix.of A *ᵥ 1) 1 x y s ∧
          (∀ (x' : Fin n → ℝ) (y' : Fin d → ℝ) (s' : Fin n → ℝ),
            IsPDOptimal (Matrix.of A) (Matrix.of A *ᵥ 1) 1 x' y' s' → x' = x ∧ y' = y ∧ s' = s) ∧
          (∀ i, i ∈ topBasis d xh ↔ 0 < x i) ∧
          (∀ i, i ∉ topBasis d xh ↔ 0 < s i) ∧
          roundBasis (Matrix.of A) xh = (x, y, s)} ≤
      ENNReal.ofReal ((n : ℝ) ^ (-(q + 1))) := by sorry

end RandomLPIPM
