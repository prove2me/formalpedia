-- Prove2me | Theorems.Thm_RandomLPIPM_theorem_1_1
-- name    : RandomLPIPM.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:11:28.069966+00:00
-- url     : https://prove2.me/theorems/de955d8f-106b-446f-b646-bcd53c046816
-- title:
--   Theorem 1.1 — a path-following IPM solves the Gaussian LP exactly in $O((\log n)^{6.5})$ iterations w.h.p.
-- statement:
--   Let $c\in(0,1/2]$ be a fixed constant and $cn\le d\le(1-c)n$, and let $A\in\mathbb R^{d\times n}$ have independent $\mathcal N(0,1)$ entries. Consider the canonical Gaussian linear program LP(A),
--   $$\min\ \mathbf 1_n^\top x\ \ \text{s.t.}\ Ax=A\mathbf 1_n,\ x\ge0,\qquad\qquad \max\ (A\mathbf 1_n)^\top y\ \ \text{s.t.}\ A^\top y+s=\mathbf 1_n,\ s\ge0 .$$
--   The paper's interior point method is: run Algorithm 1 (smoothed-divergence path following) from $(x^0,\mu_{\mathrm{start}})=(\mathbf 1,1)$ with $\mu_{\mathrm{end}}=n^{-2(q+4)}/2048$, $\varepsilon=1/6$ and Lipschitz parameter $C=C_0(\log(ed))^{4.5}$, then round the output by solving the basis system on its $d$ largest coordinates.
--
--   **Theorem.** For every $q>0$ there are constants $C_0,K>0$ and $N_0$, depending only on $c$ and $q$, such that for all $n\ge N_0$ and $cn\le d\le(1-c)n$, with probability at least $1-n^{-q}$ the method halts after at most
--   $$K(\log n)^{6.5}$$
--   iterations and returns an exact optimal primal-dual solution of LP(A). Each iteration is dominated by one linear system solve in a matrix $ADA^\top$ with $D$ positive diagonal.
--
--   Interior point methods take $O(\sqrt n\log(1/\varepsilon))$ iterations in the worst case; this is the first rigorous polylogarithmic bound for a random LP model, matching the long-standing heuristic predictions of Mizuno, Todd and Ye.
--
--   **Formalization Note** An iteration is one evaluation of the test of line 7 of Algorithm 1, which applies $P_x=I-XA^\top(AX^2A^\top)^{-1}AX$ once. The single solve of the rounding step is not counted, as in the proof. The method depends on $q$ through $\mu_{\mathrm{end}}$ and $C_0$, as in the paper.
--
--   Differences from the source:
--   - reading: There exists an IPM point method that returns the optimal primal and solutions → the paper's method (Algorithm 1 with the parameters of p.81, then the basis rounding of Theorem 8.11), only the constant C₀ existential, returning an optimal primal-dual (x, y, s); reason: the paper defines no class of IPMs and its proof exhibits this method; 'primal and solutions' is a typo for primal and dual (p.81, abstract: 'an exact optimal primal and dual solution')
--   - reading: with high probability, at most O((log n)^6.5) iterations → ∀ q > 0 ∃ C₀, K > 0, N₀ (depending only on c, q) such that for n ≥ N₀ the failure probability is ≤ n^(−q) with at most K(log n)^6.5 iterations; reason: the paper's definition of w.h.p. (p.21) with the failure exponent arbitrary, as its proofs deliver (p.56, p.81)
--   - encoding: iterations, each dominated by a linear system solve in ADAᵀ → evaluations of line 7 of Algorithm 1, each one application of P_x (one solve in AX²Aᵀ); reason: real-RAM cost claim reflected by the definition; the rounding solve is outside the count as in the proof
--   - encoding: probability of the event → outer Gaussian measure of the failure set bounded by the failure probability; reason: no measurability assumption is needed; for a measurable event it is 1 − P(event)
--   - reading: the method (unqualified) → μ_end and C₀ of the method depend on the failure exponent q; reason: the proof on p.81 sets μ_end = n^(−2(q+4))/2048 and C = C_{q+2}(log(ed))^4.5
--   - encoding: the d largest coordinates of x̂ and the solution of the basis system → topBasis, ties broken by index; roundBasis = (0, 0, 0) when the basis system has no unique solution; reason: the page leaves ties open; (0, 0, 0) is never optimal, so it counts as failure
-- source:
--   Dadush–Jiang–Kyng–Ma, Interior Point Methods Solve Random LPs in polylog(n) iterations, STOC 2027 submission (manuscript sha256 a8a320f9…), Theorem 1.1, p.6 (restated and proved p.81)

import Mathlib
import Definitions.Def_GaussianMatrix_basic
import Definitions.Def_RandomLPIPM_SolvesWithin

open Matrix MeasureTheory

namespace RandomLPIPM

/-- **Theorem 1.1 (Path following of Gaussian LP).** Dadush–Jiang–Kyng–Ma, *Interior Point Methods Solve Random LPs in polylog(n) iterations*, STOC 2027 submission (manuscript sha256 a8a320f9…), Theorem 1.1, p.6 (restated and proved
p.81).

Let `c ∈ (0, 1/2]` be a fixed constant and `cn ≤ d ≤ (1 − c)n`, and let `A ∈ ℝ^{d×n}` have independent
`N(0,1)` entries. The interior point method of the paper (Algorithm 1 on LP(A) started at
`(x⁰, μ_start) = (1, 1)`, with `μ_end = n^{−2(q+4)}/2048`, `ε = 1/6`, `C = C₀(log(ed))^{4.5}`, followed
by the basis-identification rounding of Theorem 8.11) returns the optimal primal and dual solutions
of LP(A) with high probability, using `O((log n)^{6.5})` iterations, each dominated by one linear
system solve in a matrix `ADAᵀ` with `D` positive diagonal.

**Formalization Note.** "With high probability" and `O(·)`: for every exponent `q > 0` there are
constants `C₀, K > 0` and a threshold `N₀`, depending only on `c` and `q`, such that for all `n ≥ N₀`
and `cn ≤ d ≤ (1 − c)n` the probability that the method fails (does not halt within `K(log n)^{6.5}`
line-7 evaluations with an exact optimal primal-dual solution) is at most `n^{−q}`. The method is
fixed (`SolvesWithin`); only the constant `C₀` (the paper's `C_{q+2}`) is existential, and the method
depends on `q` through `μ_end` and `C₀`, as in the proof. The failure set is measured by the (outer)
Gaussian measure. -/
theorem theorem_1_1 :
    ∀ c : ℝ, 0 < c → c ≤ 1 / 2 → ∀ q : ℝ, 0 < q →
    ∃ C₀ K : ℝ, 0 < C₀ ∧ 0 < K ∧ ∃ N₀ : ℕ, ∀ n d : ℕ, N₀ ≤ n →
    c * n ≤ d → (d : ℝ) ≤ (1 - c) * n →
    GaussianMatrix.gaussianMatrix d n {A | ¬ SolvesWithin (Matrix.of A) q C₀ (K * Real.log n ^ (13 / 2 : ℝ))} ≤
      ENNReal.ofReal ((n : ℝ) ^ (-q)) := by sorry

end RandomLPIPM
