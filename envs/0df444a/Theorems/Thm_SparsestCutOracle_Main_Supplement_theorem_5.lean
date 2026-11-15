-- Prove2me | Theorems.Thm_SparsestCutOracle_Main_Supplement_theorem_5
-- name    : SparsestCutOracle.Main.Supplement.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T05:49:56.451193+00:00
-- url     : https://prove2.me/theorems/bda9e207-6f25-4f0a-a260-de535a19d426
-- title:
--   Theorem 5 — General changing-objective primal-dual guarantee
-- statement:
--   Consider a general minimization SDP on real symmetric $n\times n$ matrices, $n\ge1$, with $M\ge1$ constraints and last constraint $A_M=-D$, $b_M=-\tau$, where $D\succ0$ and $\tau>0$. Let the generalized oracle have positive width $\rho$ relative to $D$, let $\alpha>0$, and let $0<\epsilon<1$. Use exactly
--   $$
--   \eta=\frac{\epsilon\alpha}{2\rho\tau}\le1,\qquad T\ge1,\qquad T\ge\frac{4\rho^2\tau^2\ln n}{\epsilon^2\alpha^2}.
--   $$
--   The execution of Algorithm 1 either returns its first oracle failure certificate with the promised integral feasibility and cost bound, or returns its corrected average $y^*$ and final objective $C_{\rm final}=C^{(T+1)}$, satisfying
--   $$
--   y^*\ge0,\qquad C_{\rm final}-\sum_jy_j^*A_j\succeq0,\qquad b^\top y^*\ge(1-\epsilon)\alpha.
--   $$
--   Consequently every primal feasible $X$ satisfies $C_{\rm final}\mathbin\bullet X\ge(1-\epsilon)\alpha$. This last form states the lower bound even when the primal feasible set is empty, without a totalized real infimum. No candidate is assumed primal feasible, and individual oracle answers need not be dual feasible. This is the paper's exact general-oracle companion result, rather than its graph-specific relaxed Lemma 9.
--
--   Differences from the source:
--   - encoding: the average of T oracle responses and the positive-iteration regret theorem → T≥1, retaining n=1 for every positive T; reason: the average is undefined at T=0; with n=1 the printed lower bound alone is zero, so the algorithm’s meaningful domain must be explicit
--   - encoding: M≥1 constraints indexed 1,…,M, last coordinate M → M=m+1 constraints indexed by Fin(m+1), last coordinate Fin.last m; zero-based states and canonical CFC inverse square root; reason: this is a bijective indexing convention and the actual Algorithm 1 recurrence, for arbitrary positive-definite D; oracle answers are indexed by the call number so no stationarity is imposed
--   - encoding: an approximate integral failure certificate for the underlying problem → a parameterized integral certificate type with feasibility, current-objective cost and fixed approximation factor at least one; reason: the general theorem does not prescribe an integral problem; the oracle must supply its promised certificate on failure
--   - encoding: a lower bound on the optimum for C_final → the explicit feasible dual and the same lower bound for every primal feasible objective; reason: this is the optimum lower-bound assertion without a real infimum default on an empty feasible set
-- source:
--   Robin Münk, Monika Henzinger, Harald Räcke, STOC 2027 submission #1170 (October 2026), p. 15, Theorem 5; Algorithm 1, pp. 14–15

import Mathlib
import Definitions.Def_SparsestCutOracle_Main_Supplement_PrimalDual

namespace SparsestCutOracle.Main.Supplement

/-- Theorem 5, pp.15–16. T is positive because the returned average divides by T.
No restriction n≥2: n=1 and every positive T remain in the statement. -/
theorem theorem_5 (n m : ℕ) (hn : 1 ≤ n) (S : NormalizedSDP n m)
    (C : Mat n) (hC : C.IsSymm) (ρ α ε : ℝ)
    (hρ : 0 < ρ) (hα : 0 < α) (hε : 0 < ε) (hε₁ : ε < 1)
    (hη : ε * α / (2 * ρ * S.τ) ≤ 1)
    (T : ℕ) (hT : 1 ≤ T)
    (hiterations : 4 * ρ ^ 2 * S.τ ^ 2 * Real.log n / (ε ^ 2 * α ^ 2) ≤ (T : ℝ))
    (Certificate : Type) (I : IntegralCertificates n Certificate)
    (O : GeneralOracle n m Certificate) (hO : GeneralOracleContract S I ρ O) :
    match primalDual S C ρ α ε O T with
    | Sum.inl (r, C_failure) => I.feasible r ∧ I.cost C_failure r ≤ I.ratio * α
    | Sum.inr (y, C_final) =>
      dualFeasible S C_final y ∧ (1 - ε) * α ≤ objectiveValue S y ∧
      ∀ X : Mat n, primalFeasible S X → (1 - ε) * α ≤ dot C_final X := by sorry

end SparsestCutOracle.Main.Supplement
