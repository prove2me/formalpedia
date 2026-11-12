-- Prove2me | Theorems.Thm_PQNormIPM1352_Main_lemma_9
-- name    : PQNormIPM1352.Main.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:08:39.000048+00:00
-- url     : https://prove2.me/theorems/0da2a746-3207-478b-99d5-c9c374dd92a0
-- title:
--   Lemma 9 — the vector $u$ of Algorithm 1 satisfies $\|Au\|_q/\|u\|_p\ge(1-\varepsilon)\|A\|_{p\to q}$
-- statement:
--   Let $p\ge q>1$, $\varepsilon>0$, and let $A\in\mathbb R^{m\times n}$ be non-negative with support $S$ ($s$ entries) and no all-zero row or column. Run Algorithm 1: $A' = A/A_{\max}$ with $A_{\max} = \max_S A(i,j)$, $\delta = 1/6$, the analytic center $x_0$ of Lemma 7, $\eta_0 = \sqrt2/(10\sqrt s)$, the iteration count $T = \max(\lceil100\sqrt s\log(s/\varepsilon)\rceil, \lceil21\sqrt\nu\log(7\nu/(6\varepsilon\eta_0))\rceil)$ with $\nu = 3s+2$, and $T$ steps
--   $$x_{t+1} = x_t + \tilde\Delta_t,\qquad \eta_{t+1} = \Big(1+\frac1{20\sqrt{3s+2}}\Big)\eta_t,$$
--   where each $\tilde\Delta_t$ is any $\delta$-approximate Newton step (3) of $\Phi_{\eta_t} = F + \eta_t\langle -\bar a', \cdot\rangle$ at $x_t$. Then the returned vector $u = (y_T/Y_T)^{1/p}$, $Y_T = \sum_j y_T(j)$, satisfies
--   $$\frac{\|Au\|_q}{\|u\|_p} \ge (1-\varepsilon)\,\|A\|_{p\to q}.$$
--
--   This is the correctness of Algorithm 1; no rounding of the final iterate is needed.
--
--   Differences from the source:
--   - encoding: the non-negative matrix after removing all-zero rows and columns, a standing assumption of §3 (p. 7) → a sparsity pattern with every row and column occupied (`Preprocessed`) and the barrier on ℝ^{m+n+s}; reason: the paper removes such rows and columns before (5) and works with the support S only
--   - reading: T = ⌈100√s log(s/ε)⌉ (Step 4), proved sufficient only for s ≥ 20 (footnote 4) → T = max(⌈100√s log(s/ε)⌉, ⌈21√ν log(7ν/(6εη₀))⌉); reason: the second term is the count of the proof of Theorem 5 (p. 25), valid for every s; the two agree for s ≥ 16, so the algorithm is unchanged where the paper analyses it
--   - generalization: the Newton steps computed by Algorithm 4 (NewtonSolve) → any δ-approximate Newton steps (3) with δ = 1/6; reason: Lemma 11 shows that every output of Algorithm 4 is such a step, so the statement specializes to Algorithm 1
--   - encoding: the vector u ∈ ℝⁿ padded with zeros on removed columns → u on the columns of the preprocessed pattern; reason: zero rows and columns change neither ‖Au‖_q, ‖u‖_p nor ‖A‖_{p→q}
-- source:
--   Marco Pirazzini, Daniel Spielman, A Fast and Accurate Algorithm for the p → q Norm of Sparse Non-Negative Matrices, STOC 2027 submission #1352 (October 2026), Lemma 9, printed p. 11 (PDF p. 12); Algorithm 1, p. 9; footnote 4, p. 11

import Mathlib
import Definitions.Def_PQNormIPM1352_Main_Barrier

open Matrix

namespace PQNormIPM1352.Main

/-- **Lemma 9** (Pirazzini–Spielman, STOC 2027 #1352, p. 11). Let `p ≥ q > 1`, `ε > 0`, and let `A`
be a non-negative matrix given by a preprocessed pattern (no all-zero row or column) with entries
`a_k > 0`. Run Algorithm 1: `A' = A / A_max`, `δ = 1/6`, `x₀` and `η₀` as in Lemmas 7–8,
`T = iterCount s ε`, and `T` path-following steps `x ← x + Δ̃`, `η ← (1 + 1/(20√(3s+2))) η`, where each
`Δ̃` is any δ-approximate Newton step (3) of `Φ_η = F + η⟨−ā', ·⟩`. The returned vector
`u = (y_T / Y_T)^{1/p}` satisfies `‖Au‖_q / ‖u‖_p ≥ (1 − ε) ‖A‖_{p→q}`. -/
theorem lemma_9 {m n s : ℕ} (P : SparsePattern m n s) (hP : P.Preprocessed) (a : Fin s → ℝ)
    (ha : ∀ k, 0 < a k) (p q ε : ℝ) (hq : 1 < q) (hqp : q ≤ p) (hε : 0 < ε)
    (x : ℕ → Vec (m + n + s))
    (hx : IsApproxPathRun (P.barrierF p q) (P.cvec fun k => a k / ⨆ l, a l) (nuParam s) (1 / 6)
      (eta0 s) (P.initPoint p q) x) :
    (1 - ε) * opNormPQ (P.toMatrix a) p q ≤
      pNorm q (P.toMatrix a *ᵥ P.outputVec p (x (iterCount s ε))) /
        pNorm p (P.outputVec p (x (iterCount s ε))) := by sorry

end PQNormIPM1352.Main
