-- Prove2me | Theorems.Thm_TruncLowDeg_Recovery_theorem_6_1
-- name    : TruncLowDeg.Recovery.theorem_6_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:25:20.807751+00:00
-- url     : https://prove2.me/theorems/ebc41fb6-9a28-4550-b555-a191dc06f6f0
-- title:
--   Theorem 6.1 — learning a Gaussian truncated to a set of boundary vanishing degree $k$ from $(d/\alpha_0)^{O(k)}/(\delta\varepsilon^2)$ samples in time $n\,d^{O(k)}$
-- statement:
--   Let $\alpha_0\in(0,1]$, $k\ge1$, $\mu_0\in\mathbb R^d$, $\Sigma_0\succ0$, and let $S_0\subseteq\mathbb R^d$ with $\mathrm{BVD}(S_0)\le k$ and $\mathcal N(\mu_0,\Sigma_0)(S_0)\ge\alpha_0$. For every $\varepsilon,\delta\in(0,1)$, given
--   $$n\ \ge\ \frac{1}{\delta\varepsilon^2}\cdot\Big(\frac d{\alpha_0}\Big)^{O(k)}$$
--   independent samples from $\mathcal N(\mu_0,\Sigma_0)|_{S_0}$, there is an algorithm that runs in $n\,d^{O(k)}$ time and, with probability at least $1-\delta$, outputs $\hat\mu_0\in\mathbb R^d$ and $\hat\Sigma_0\succ0$ such that
--   $$d_{TV}\big(\mathcal N(\mu_0,\Sigma_0),\mathcal N(\hat\mu_0,\hat\Sigma_0)\big)\le\varepsilon .$$
--   Formally: there are a universal constant $C>0$ and one admissible program $P$ of the deterministic unit-cost real RAM with square root such that for every $d\ge1$, $k\ge1$, $\alpha_0\in(0,1]$, $\mu_0$, $\Sigma_0\succ0$, every $S_0$ with $\mathrm{BVD}(S_0)\le k$ and $\mathcal N(\mu_0,\Sigma_0)(S_0)\ge\alpha_0$, every $\varepsilon,\delta\in(0,1)$ and every $n\ge(1/(\delta\varepsilon^2))(d/\alpha_0)^{Ck}$: (i) on input $(d,k,n,\alpha_0,\varepsilon,\delta,X_1,\dots,X_n)$ $P$ halts within $C\,n\,d^{Ck}$ steps for every table; (ii) under $n$ i.i.d. samples from $\mathcal N(\mu_0,\Sigma_0)|_{S_0}$, the set of tables on which the output is not a pair with $\hat\Sigma_0\succ0$ and total variation distance at most $\varepsilon$ has probability at most $\delta$. The program knows $k$ and $\alpha_0$ but neither $S_0$ nor its boundary vanishing polynomial. For truncation sets of constant boundary vanishing degree (halfspaces, degree-$k$ polynomial threshold functions, intersections of a constant number of them) this gives polynomial sample complexity and running time.
--
--   Differences from the source:
--
--   - reading: "there is an algorithm that runs in n d^{O(k)} time" → one `Admissible` program P of the deterministic unit-cost real RAM with square root (`Machine`), fixed before the instance; time = number of executed instructions; reason: the paper names no machine; the reading has no eigen-, SVD- or matrix-square-root primitive and no randomness, so it does not strengthen the model
--   - reading: d^{O(k)} and (d/α₀)^{O(k)} → d^{C·k} and (d/α₀)^{C·k} with the same universal C as the time constant; reason: the literal and stronger reading; at d = 1 it gives a k-free time bound C·n (finding I1), kept as printed
--   - encoding: the algorithm's input → `initConfig d k n α₀ ε δ X`: pointers d, k, n and memory α₀, ε, δ, then the samples row by row; nothing about µ₀, Σ₀, S₀ or the boundary polynomial; reason: the paper: the algorithm knows k and α₀ but neither S nor the boundary vanishing polynomial (p. 3)
--   - encoding: runs in n d^{O(k)} time → for every table of n points the program halts within C·n·d^{C·k} steps; reason: worst case on every input (the proof: "always runs in time n·d^{O(k)}")
--   - encoding: with probability at least 1 − δ, outputs µ̂₀ and Σ̂₀ ≻ 0 with d_TV ≤ ε → the product measure of the tables on which the halted output is not `some (µ̂₀, Σ̂₀)` with Σ̂₀ positive definite and `tvDist` ≤ ε is at most δ; reason: failure-set form; Fail (reject) counts as failure
--   - reading: ℝ^d with the dimension left implicit → hypothesis `1 ≤ d`; reason: the paper works in ℝ^d with d ≥ 1 (coordinates j ∈ {1, …, d}); at d = 0 the expressions d^{O(k)}, (d + L²) and d·t^{1/k} degenerate and the paper never considers it
--   - encoding: ℝ^d, coordinates j ∈ {1, …, d} → `Vec d = EuclideanSpace ℝ (Fin d)`, 0-based coordinates `Fin d`; reason: Lean convention; same instances
--   - encoding: N(µ, Σ)|S → `truncGaussian µ Σ S = cond (multivariateGaussian µ Σ) S`; reason: the definition of §5.1; it needs no measurability of S
--   - encoding: BVD(S₀) ≤ k → `BVD S₀ ≤ (k : ℕ∞)`; reason: BVD takes values in ℕ ∪ {∞}
-- source:
--   Vári-Kakas, Wiedmer, A General Approach to Polynomial-Time Truncated Learning via Low-Degree Moments, STOC 2027 submission (manuscript sha256 613f0e39…), p. 25, Theorem 6.1 (full version of Theorem 1.4, p. 3); proof p. 33

import Definitions.Def_TruncLowDeg_Recovery_Basic
import Definitions.Def_TruncLowDeg_Recovery_Machine
import Definitions.Def_FoundationsRL_DECLower_tvDist

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder

namespace TruncLowDeg.Recovery

/-- Theorem 6.1 (p. 25; full version of Theorem 1.4). There are a universal constant `C > 0`
and one admissible program `P` of the deterministic unit-cost real RAM with square root such
that, for every `d ≥ 1`, `k ≥ 1`, `α₀ ∈ (0, 1]`, `µ₀ ∈ ℝ^d`, `Σ₀ ≻ 0`, every `S₀ ⊆ ℝ^d` with
`BVD(S₀) ≤ k` and `N(µ₀, Σ₀)(S₀) ≥ α₀`, every `ε, δ ∈ (0, 1)` and every
`n ≥ (1/(δε²)) (d/α₀)^{Ck}`:
(i) on input `(d, k, n, α₀, ε, δ, X₁, …, X_n)`, for every table of `n` points, `P` halts within
`C n d^{Ck}` steps;
(ii) when `X₁, …, X_n` are i.i.d. from `N(µ₀, Σ₀)|S₀`, the set of tables on which the output is
not a pair `(µ̂₀, Σ̂₀)` with `Σ̂₀ ≻ 0` and `d_TV(N(µ₀, Σ₀), N(µ̂₀, Σ̂₀)) ≤ ε` has probability at
most `δ`. -/
theorem theorem_6_1 :
    ∃ C : ℝ, 0 < C ∧ ∃ P : Program, Admissible P ∧
      ∀ (d k : ℕ) (α₀ : ℝ) (μ₀ : Vec d) (Sig₀ : Mat d) (S₀ : Set (Vec d)) (ε δ : ℝ) (n : ℕ),
      1 ≤ d → 1 ≤ k → 0 < α₀ → α₀ ≤ 1 → Sig₀.PosDef → BVD S₀ ≤ (k : ℕ∞) →
      ENNReal.ofReal α₀ ≤ gaussian μ₀ Sig₀ S₀ → 0 < ε → ε < 1 → 0 < δ → δ < 1 →
      1 / (δ * ε ^ 2) * ((d : ℝ) / α₀) ^ (C * k) ≤ n →
        (∀ X : Fin n → Vec d, ∃ t : ℕ, (t : ℝ) ≤ C * n * (d : ℝ) ^ (C * k) ∧
          Halted P (run P (initConfig d k n α₀ ε δ X) t)) ∧
        (Measure.pi fun _ : Fin n => truncGaussian μ₀ Sig₀ S₀)
            {X | ∃ t : ℕ, Halted P (run P (initConfig d k n α₀ ε δ X) t) ∧
              ¬ ∃ (μh : Vec d) (Sh : Mat d),
                output P d (run P (initConfig d k n α₀ ε δ X) t) = some (μh, Sh) ∧
                Sh.PosDef ∧
                FoundationsRL.DECLower.tvDist (gaussian μ₀ Sig₀) (gaussian μh Sh) ≤ ε} ≤
          ENNReal.ofReal δ := by sorry

end TruncLowDeg.Recovery
