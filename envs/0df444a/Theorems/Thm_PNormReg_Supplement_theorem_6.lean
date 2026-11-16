-- Prove2me | Theorems.Thm_PNormReg_Supplement_theorem_6
-- name    : PNormReg.Supplement.theorem_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T17:55:47.754691+00:00
-- url     : https://prove2.me/theorems/dc9435bf-6aea-4bc7-b3d7-ce80146393ed
-- title:
--   Theorem 6, p.11 — an $\eta$-improvement oracle from one $\ell_2$-$\ell_q$ matrix game, in time $\widetilde O(n^{\omega(1,a,a)})$ plus the game solve
-- statement:
--   Let $A\in\mathbb R^{n\times d}$ have full column rank, $b\in\mathbb R^n$, $x'\in\mathbb R^d$, $p\in[1,\infty]$, $\eta>0$, $\delta\in(0,1)$, $1/p+1/q=1$ (with $1/\infty=0$) and $d=n^a$. Then $\mathrm{ApproxImprovementOracle}(\eta,x',\delta)$ can be implemented in $\widetilde O(n^{\omega(1,a,a)})$ time plus the time to compute, with failure probability at most $\delta/2$, an $\eta^{-1}$-additive approximate solution to
--
--   $$\min_{x\in B^r_2}\max_{y\in B^n_q}y^\top(Mx-c),\tag{5}$$
--
--   where $r=\widetilde O(d)$, $M\in\mathbb R^{n\times r}$ and $c\in\mathbb R^n$ satisfy $\|M\|_{p,2}\le16d^{\max\{1/p,1/2\}}$ and $\|c\|_p\le1$.
--
--   Precisely: for every $\tau>0$ there are one oracle program and constants $C>0$, $K\in\mathbb N$ such that, for every valid randomized solver of (5), with $N=\max(n,2)$ and $L=\log(2+n+1/\delta)$:
--
--   1. on every program tape and every choice of solver tapes the run halts after at most $C\,N^{\omega(1,a,a)+\tau}L^K$ non-oracle steps and at most one solver call; that call asks for accuracy $\eta^{-1}$ with failure parameter $\delta/2$ on a game with $r\le C\,d\,L^K$ columns, $\|M\|_{p,2}\le16d^{\max\{1/p,1/2\}}$ and $\|c\|_p\le1$;
--   2. with probability at least $1-\delta$ the output $\hat\Delta$ satisfies (4) at $x'$:
--
--   $$\|A(\hat\Delta+x')-b\|_p\le\eta^{-1}\|Ax'-b\|_p+\|A(\Delta+x')-b\|_p\quad\text{for every }\Delta\text{ with }\|A\Delta\|_p\le2\|Ax'-b\|_p.$$
--
--   This is the paper's key reduction: each improvement step of regression costs one well-normalized matrix game.
--
--   **Formalization Note** The game's primal objective $\max_{y\in B^n_q}y^\top(Mx-c)$ is written as $\|Mx-c\|_p$ (norm duality). $\omega(1,a,a)$ is `PNormReg.Supplement.RectOmega`, with $a=\log d/\log N$. Input: dense $A$, $b$, header $1/p,\eta,\delta,x'$; output $\hat\Delta$ in the base machine's output cells.
--
--   Differences from the source:
--   - reading: "there is an algorithm" (no machine named) → one finite admissible program of the base machine extended by an oracle-call instruction (PNormReg.Supplement.OracleMachine); reason: the paper fixes no machine; same reading as the published goal Theorem 2
--   - reading: Õ(n^{ω(1,a,a)}) with d = n^a (footnote 2) → for every τ > 0 one program with C, K: C·N^{ω(1,a,a)+τ}·(log(2 + n + 1/δ))^K, N = max(n, 2), a = log d / log N; reason: footnote 2 pins the hidden factors; Theorem 6 has no ϵ, and η enters only the solver's cost; N = n for n ≥ 2
--   - reading: "plus the time to compute, with failure probability at most δ/2, an η^{−1}-additive approximate solution to (5)" → the solver is an oracle costing 0 work; at most one call, with accuracy exactly η^{−1} and failure parameter exactly δ/2; every valid randomized solver (private tape, correct with probability ≥ 1 − δ_g, jointly measurable); reason: the formal content of an oracle-relative running time; the proof makes at most one call (none if f_p(x′) = 0)
--   - reading: r = Õ(d) → r ≤ C·d·(log(2 + n + 1/δ))^K for every game passed; reason: footnote 2
--   - encoding: primal objective max_{y∈B^n_q} y⊤(Mx − c) → ∥Mx − c∥_p; reason: norm duality max_{∥y∥_q≤1} y⊤v = ∥v∥_p (p.14); same values
--   - encoding: ω(1,a,a), the exponent of k^1 × k^a by k^a × k^a multiplication in time (p.8) → omegaOneAA, the infimum of admissible exponents for k × ⌈k^a⌉ by ⌈k^a⌉ × ⌈k^a⌉ multiplication by arithmetic straight-line programs over ℝ (the OAI cost model of the base mission's ω); reason: the same convention as the published goal's ω; the paper's ω(a, b, c) is that of [WXXZ24], an arithmetic-complexity exponent
--   - encoding: p ∈ [1, ∞], q conjugate, ∥M∥_{∞,2} = max_i ∥M_{i:}∥₂ → pInv = 1/p ∈ [0, 1]; ∥·∥_p is the sup norm at pInv = 0; reason: the paper's 1/∞ = 0
--   - encoding: input x′, A, b, p, η, δ → dense layout: n, d; 1/p, η, δ, x′, A row-major, b; output Δ̂ in cells −1 − j; reason: the paper names no format; the bound pays for reading dense A
--   - encoding: ApproxImprovementOracle(η, x′, δ): (4) with probability at least 1 − δ → a measurable set of joint tapes of probability ≥ 1 − δ on which the halted output satisfies (4) at x′, the minimum written as "for every Δ in the ball"; reason: the minimum exists, so "for every x" is the same condition; same as Theorem 2
--   - encoding: A ∈ ℝ^{n×d} (d ≥ 1 implicit) → 1 ≤ d; reason: excludes only the empty problem, where a zero time bound would forbid halting
-- source:
--   Adil, Bullins, O'Carroll, Sidford, Solving p-norm regression in matrix multiplication time, STOC 2027 submission (manuscript sha256 e335b2fa…), Theorem 6, p.11 (PDF p.12); Definition 1, p.8; ω(a, b, c), p.8; problem (1) and footnotes 1–2, p.1

import Mathlib
import Definitions.Def_PNormReg_Supplement_RectOmega
import Definitions.Def_PNormReg_Supplement_Oracles

open Matrix

namespace PNormReg

namespace Supplement

/-- **Theorem 6** (an `η`-improvement oracle from one `ℓ₂`-`ℓ_q` matrix game).

Adil, Bullins, O'Carroll, Sidford, *Solving p-norm regression in matrix multiplication time*, STOC 2027
submission (manuscript sha256 e335b2fa…), Theorem 6, p.11 (PDF p.12); Definition 1, p.8; ω(a, b, c), p.8; problem (1) and
footnotes 1–2, p.1.

"Let x′ ∈ R^d, p ∈ [1, ∞], η > 0, and δ ∈ (0, 1), and define q by 1/p + 1/q = 1, with 1/∞ = 0. Writing
d = n^a, an η-improvement oracle, ApproxImprovementOracle(η, x′, δ), can be implemented in Õ(n^{ω(1,a,a)})
time plus the time to compute, with failure probability at most δ/2, an η^{−1}-additive approximate
solution to min_{x∈B^r_2} max_{y∈B^n_q} y⊤(Mx − c), (5) where r = Õ(d), M ∈ R^{n×r}, and c ∈ R^n satisfy
∥M∥_{p,2} ≤ 16d^{max{1/p,1/2}} and ∥c∥_p ≤ 1."

For every `τ > 0` there are one admissible oracle program `P` and `C > 0`, `K ∈ ℕ` such that for all
`n`, `d ≥ 1`, full column rank `A`, `b`, `p ∈ [1, ∞]` (as `pInv = 1/p`), `η > 0`, `δ ∈ (0, 1)`, `x′`
and every valid randomized solver `O` of game (5), with `N = max(n, 2)`, `a = log d / log N` and
`L = log(2 + n + 1/δ)`:
1. on every program tape and every family of oracle tapes the run halts with non-oracle work at most
   `C·N^{ω(1,a,a)+τ}·L^K` and at most one solver call; every call asks for accuracy `η^{−1}` with failure
   parameter `δ/2`, on a game with `r ≤ C·d·L^K` columns, `∥M∥_{p,2} ≤ 16·d^{max{1/p,1/2}}` and
   `∥c∥_p ≤ 1`;
2. on a measurable set of joint tapes of probability at least `1 − δ` the output `Δ̂` satisfies (4) at
   `x′`: `f_p(Δ̂ + x′) ≤ η^{−1}f_p(x′) + f_p(Δ + x′)` for every `Δ` with `∥AΔ∥_p ≤ 2f_p(x′)`.

**Formalization Note.**
* "Implemented in `Õ(n^{ω(1,a,a)})` time plus the time to compute … (5)" is read as an oracle program
  whose oracle is any valid randomized solver of (5): the solver costs `0` work, and the program bounds
  the number of solver calls and every game it passes. Solver answers are correct with probability at
  least `1 − δ_g` on that call's own tape; the solver is jointly measurable.
* Game (5)'s primal objective `max_{y ∈ B^n_q} y⊤(Mx − c)` is written as `∥Mx − c∥_p` (norm duality).
* `ω(1, a, a)` is `omegaOneAA` on the base mission's arithmetic cost model; `d = n^a` with
  `a = log d / log N`, exact for `n ≥ 2`. `Õ` (footnote 2): `τ` in the exponent is the `n^{o(1)}`, `L^K`
  the polylogarithmic factor; `η` enters no bound (the solver's cost carries it). No `p` factor: the
  theorem says `Õ`, for every `p ∈ [1, ∞]`.
* `∥M∥_{∞,2} = max_i ∥M_{i:}∥₂` at `p = ∞`; `q = 1` at `p = ∞` and `q = ∞` at `p = 1`, through `pNorm`.
* Input: `denseInput ([pInv, η, δ] ++ x′) A b`; output `Δ̂` in cells `−1 − j`; oracle interface
  `gameIface n`. `d ≥ 1`: the problem is empty at `d = 0`. -/
theorem theorem_6 :
    ∀ τ : ℝ, 0 < τ →
      ∃ (P : OProgram) (_ : OAdmissible P) (C : ℝ) (K : ℕ), 0 < C ∧
        ∀ (n d : ℕ), 1 ≤ d → ∀ (A : Matrix (Fin n) (Fin d) ℝ) (b : Fin n → ℝ),
          Function.Injective A.mulVec →
          ∀ pInv η δ : ℝ, 0 ≤ pInv → pInv ≤ 1 → 0 < η → 0 < δ → δ < 1 →
          ∀ x' : Fin d → ℝ,
          ∀ O : GameQuery → (ℕ → Bool) → (ℕ → ℝ),
            ValidOracle (gameSpec n pInv) (fun q => q.2.2.1) O →
            (∀ (ω : ℕ → Bool) (Ω : ℕ → ℕ → Bool), ∃ t : ℕ,
              (orun P (gameIface n) O (denseInput ([pInv, η, δ] ++ List.ofFn x') A b) ω Ω
                t).base.halted = true ∧
              ((orun P (gameIface n) O (denseInput ([pInv, η, δ] ++ List.ofFn x') A b) ω Ω
                t).base.work : ℝ) ≤
                C * ((max n 2 : ℕ) : ℝ) ^ (omegaOneAA (aExp n d) + τ) *
                  Real.log (2 + n + 1 / δ) ^ K ∧
              (orun P (gameIface n) O (denseInput ([pInv, η, δ] ++ List.ofFn x') A b) ω Ω
                t).calls ≤ 1 ∧
              ∀ q ∈ (orun P (gameIface n) O (denseInput ([pInv, η, δ] ++ List.ofFn x') A b) ω Ω
                  t).log,
                q.2.1 = η⁻¹ ∧ q.2.2.1 = δ / 2 ∧
                  (q.1 : ℝ) ≤ C * d * Real.log (2 + n + 1 / δ) ^ K ∧
                  rowNorm pInv (gameMat n q) ≤ 16 * (d : ℝ) ^ (max pInv (1 / 2)) ∧
                  pNorm pInv (gameVec n q) ≤ 1) ∧
            ∃ E : Set ((ℕ → Bool) × (ℕ → ℕ → Bool)), MeasurableSet E ∧
              1 - δ ≤ (jointTape E).toReal ∧
              ∀ z ∈ E, ∀ t : ℕ,
                (orun P (gameIface n) O (denseInput ([pInv, η, δ] ++ List.ofFn x') A b) z.1 z.2
                  t).base.halted = true →
                ImproveGuarantee A b pInv η x' (outputVec d
                  (orun P (gameIface n) O (denseInput ([pInv, η, δ] ++ List.ofFn x') A b) z.1 z.2
                    t).base) := by sorry

end Supplement

end PNormReg
