-- Prove2me | Theorems.Thm_PrefixVR_Supplement_theorem_4
-- name    : PrefixVR.Supplement.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:53:23.878046+00:00
-- url     : https://prove2.me/theorems/63b0d848-e90a-4bdb-b424-e694e337da5c
-- title:
--   Theorem 4 — proximal batched method: $\mathbb E\|G_\eta(x_{\tau+1})\|^2\le\mathbb E\,\mathrm{dist}^2(0,\partial F(x_{\tau+1}))\le 228K_b\Delta_F/(5T)$
-- statement:
--   Consider the composite problem $\min_x F(x):=f(x)+g(x)$ (16) with $f=\frac1n\sum_{i=1}^n f_i$ satisfying **Assumption 3** with $L_f>0$, $\delta\ge0$ ($f$ itself need not be bounded below), $g:\mathbb R^d\to\mathbb R\cup\{+\infty\}$ proper, closed and convex, $F_*:=\inf_x F(x)>-\infty$, $x_1\in\operatorname{dom}g$ and $\Delta_F:=F(x_1)-F_*$. Let $1\le b\le\lfloor\sqrt n\rfloor$, $q=\lceil n/b\rceil$, and
--   $$
--   K_b:=L_f+\delta\sqrt{q/b},\qquad \eta=\frac1{4K_b},
--   $$
--   and run Algorithm 2 for $T\ge1$ updates with the exact proximal map $\operatorname{prox}_{\eta g}$. With the gradient mapping $G_\eta(x)=\frac1\eta\big(x-\operatorname{prox}_{\eta g}(x-\eta\nabla f(x))\big)$, $\partial F(x)=\nabla f(x)+\partial g(x)$ and $\operatorname{dist}(0,S)=\inf_{z\in S}\|z\|$:
--   1. on every outcome $\partial F(x_{\tau+1})\neq\emptyset$;
--   2. $$\mathbb E\,\big\|G_\eta(x_{\tau+1})\big\|^2\le\mathbb E\,\operatorname{dist}^2\big(0,\partial F(x_{\tau+1})\big)\le\frac{228\,K_b\,\Delta_F}{5T};\qquad(21)$$
--   3. on every outcome the method makes at most $n+5bT$ component-gradient queries and exactly $T$ proximal evaluations.
--
--   The returned point $x_{\tau+1}$ is produced by a proximal step, so the guarantee certifies stationarity at the point the algorithm outputs. Batching trades proximal calls for gradient queries per update without changing the order of the gradient complexity; the estimator still stores a constant number of $d$-dimensional vectors.
--
--   **Formalization Note** "Proper, closed, convex" and the exact proximal map are the published `ThreeOpSplitting.ConvexRates.IsProperClosedConvex` and `IsProx`; $G_\eta$ is the published `NesterovFB.Rates.gradMap`; $\partial g$ is the published `DCAExtrap.convexSubdiff`. $\operatorname{dist}(0,S)$ is `Metric.infDist 0 S`, which is $0$ (not $+\infty$) on the empty set, so clause 1 is stated explicitly. The counts are lengths of the logs written by the two oracles; the $O(d)$ memory clause is read structurally (the state is four vectors; batches are streamed through running sums).
--
--   Differences from the source:
--   - encoding: f satisfies Assumption 3 → the published PrefixVR.Assumption3 fi gf Lf δ; reason: as in Theorems 2 and 3; the gradient of f is the average of the component gradients
--   - encoding: g : ℝᵈ → ℝ ∪ {+∞} proper, closed, convex → g : ℝᵈ → EReal with the published ThreeOpSplitting.ConvexRates.IsProperClosedConvex g (never −∞, finite somewhere, lower semicontinuous, convex epigraph); reason: the standard extended-real encoding of the same class
--   - encoding: the exact proximal map prox_{ηg}(z) := argmin_y {g(y) + ‖y − z‖²/(2η)} → a map P with the published IsProx η g P (P z minimizes g y + ‖y − z‖²/(2η) for every z); reason: for proper closed convex g and η > 0 the minimizer exists and is unique, so P is prox_{ηg}
--   - encoding: F_* := inf F > −∞, x₁ ∈ dom g, Δ_F := F(x₁) − F_* → compositeStar fi g ≠ ⊥, g x₁ ≠ ⊤, Δ_F = (compositeObj fi g x₁ − compositeStar fi g).toReal; reason: both terms of Δ_F are finite under these hypotheses, so the real number is exact
--   - encoding: 1 ≤ b ≤ ⌊√n⌋, q = ⌈n/b⌉, η = 1/(4K_b) → 1 ≤ b ≤ Nat.sqrt n, q = numBlocks n b = ⌈(n:ℝ)/b⌉₊, a variable η with hη : η = 1/(4(L_f + δ√(q/b))); reason: Nat.sqrt n = ⌊√n⌋; the equation pins η
--   - encoding: dist(0, S) := inf_{z∈S}‖z‖ with inf ∅ = +∞ → Metric.infDist 0 S, together with clause 1: ∂F(x_{τ+1}) is nonempty on every outcome; reason: the two agree on nonempty sets; since every outcome has positive probability, the paper's finite bound (21) under its +∞ convention already forces nonemptiness on every outcome (proved on p.25), so the conjunction is the paper's statement
--   - encoding: G_η(x) := (1/η)(x − prox_{ηg}(x − η∇f(x))) and ∂F(x) := ∇f(x) + ∂g(x) → the published NesterovFB.Rates.gradMap f P η and subdiffF (with the published DCAExtrap.convexSubdiff); reason: the same formulas
--   - encoding: the expectation over τ and all samples of Algorithm 2 → the uniform average expect2 over the finite sample space Sample2 n b T; reason: independent uniform draws (batches with replacement) on finite sets have the uniform product law; unused coordinates change no expectation
--   - encoding: at most n + 5bT component-gradient queries and exactly T proximal evaluations → the gradient log has length ≤ n + 5bT and the proximal log has length T, on every outcome; reason: the algorithm reaches ∇fᵢ and prox_{ηg} only through logging oracles; one call is one entry
--   - reading: the gradient estimator uses O(d) working memory → structural: Algorithm 2 is the iteration of step2 on the four-vector record PrefixVR.State d, every batch sum streamed through one running vector; no separate conjunct; reason: App. F, p.25, describes the memory as a constant number of vectors independent of b and n; there is no machine model to state it in
--   - encoding: components i ∈ [n] → Fin n with NeZero n, paper index i is i − 1; reason: Lean convention; n ≥ 1 is the standing setting of a finite sum
-- source:
--   Jiang, Wang, Yang, Li, Zhang, Memory-efficient Finite-sum Optimization without Full Gradient Refreshes (manuscript, sha256 ed33106a…), §6, Theorem 4, Eq. (21), p.10 (PDF p.10); conditions §6, p.9, (16)–(18); proof App. E–F, pp.20–25

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_KatyushaNs_favg
import Definitions.Def_PrefixVR_Variation
import Definitions.Def_PrefixVR_Assumption3
import Definitions.Def_PrefixVR_step
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_NesterovFB_Rates_Algorithm
import Definitions.Def_DCAExtrap_convexSubdiff
import Definitions.Def_PrefixVR_Supplement_compositeObj
import Definitions.Def_PrefixVR_Supplement_step2
import Definitions.Def_PrefixVR_Supplement_Sample2
import Definitions.Def_PrefixVR_Supplement_run2

namespace PrefixVR.Supplement

open PrefixVR

/-- **Theorem 4.** Jiang, Wang, Yang, Li, Zhang, *Memory-efficient Finite-sum Optimization without
Full Gradient Refreshes* (manuscript, sha256 ed33106a…), §6, Theorem 4, Eq. (21), p.10: "Under the
conditions of this section, let K_b := L_f + δ√(q/b), η = 1/(4K_b). Algorithm 2 satisfies
𝔼‖G_η(x_{τ+1})‖² ≤ 𝔼 dist²(0, ∂F(x_{τ+1})) ≤ 228K_bΔ_F/(5T). It makes at most n + 5bT
component-gradient queries and exactly T proximal evaluations. The gradient estimator uses O(d)
working memory." The conditions of §6, p.9: `g : ℝᵈ → ℝ ∪ {+∞}` proper, closed, convex; `f`
satisfies Assumption 3; `F_* := inf_x F(x) > −∞`; `x₁ ∈ dom g`; `Δ_F := F(x₁) − F_*`; the exact
proximal map; `1 ≤ b ≤ ⌊√n⌋`, `q = ⌈n/b⌉` (18). Proof: App. E–F, pp.20–25.

For every `n ≥ 1`, components `fᵢ` with gradient maps `gf i = ∇fᵢ` satisfying Assumption 3 with
`L_f, δ`, proper closed convex `g` with `F_* > −∞`, `x₁ ∈ dom g`, `1 ≤ b ≤ ⌊√n⌋`,
`η = 1/(4K_b)`, the exact proximal map `P = prox_{ηg}`, and `T ≥ 1`, Algorithm 2 satisfies:
1. on every outcome, `∂F(x_{τ+1})` is nonempty (so `dist(0, ∂F(x_{τ+1}))` is a finite infimum);
2. `𝔼‖G_η(x_{τ+1})‖² ≤ 𝔼 dist²(0, ∂F(x_{τ+1}))`;
3. `𝔼 dist²(0, ∂F(x_{τ+1})) ≤ 228 K_b Δ_F / (5T)`;
4. on every outcome, at most `n + 5bT` component-gradient queries and exactly `T` proximal
   evaluations.

**Formalization Note.** `ℝᵈ` is `EuclideanSpace ℝ (Fin d)`, `f = KatyushaNs.favg fi`, `∇f` is
Mathlib's `gradient`. "Proper, closed, convex" is the published
`ThreeOpSplitting.ConvexRates.IsProperClosedConvex` (never `−∞`, finite somewhere, lower
semicontinuous, convex epigraph). The exact proximal map is a function `P` with the published
`ThreeOpSplitting.ConvexRates.IsProx η g P` (`P z` minimizes `g y + ‖y − z‖²/(2η)` for every
`z`); for proper closed convex `g` and `η > 0` this minimizer exists and is unique, so `P` is
`prox_{ηg}`. `G_η` is the published `NesterovFB.Rates.gradMap (f) P η`
(`(1/η)(x − P(x − η∇f(x)))`). `∂F(x) = ∇f(x) + ∂g(x)` (`subdiffF`) with the published convex
subdifferential `DCAExtrap.convexSubdiff`. `dist(0, S)` is `Metric.infDist 0 S`, which equals
the paper's `inf_{z∈S}‖z‖` on nonempty `S`; clause 1 rules out the empty case (where the paper's
value is `+∞` and Mathlib's is `0`). `F_* > −∞` is `compositeStar fi g ≠ ⊥`; `x₁ ∈ dom g` is
`g x₁ ≠ ⊤`; `Δ_F` is the real number `(F(x₁) − F_*).toReal` (both terms finite). `⌊√n⌋` is
`Nat.sqrt n`, `q` is `numBlocks n b = ⌈n/b⌉₊`. The counts are the lengths of the logs written by
the gradient and proximal oracles. The memory clause is read structurally: Algorithm 2 is the
iteration of `step2` on the four-vector record `PrefixVR.State d`, with every batch sum streamed
through one running vector; the proximal oracle's internal workspace is excluded (p.4). -/
theorem theorem_4 {n d : ℕ} [NeZero n] (fi : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (gf : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (Lf δ : ℝ)
    (hA3 : Assumption3 fi gf Lf δ)
    (g : EuclideanSpace ℝ (Fin d) → EReal)
    (hg : ThreeOpSplitting.ConvexRates.IsProperClosedConvex g)
    (hFstar : compositeStar fi g ≠ ⊥)
    (x₁ : EuclideanSpace ℝ (Fin d)) (hx₁ : g x₁ ≠ ⊤)
    (b : ℕ) (hb1 : 1 ≤ b) (hbn : b ≤ Nat.sqrt n)
    (η : ℝ) (hη : η = 1 / (4 * (Lf + δ * Real.sqrt ((numBlocks n b : ℝ) / b))))
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hP : ThreeOpSplitting.ConvexRates.IsProx η g P)
    (T : ℕ) (hT : 1 ≤ T) :
    (∀ ω : Sample2 n b T, (subdiffF fi g (output2 gf P η b x₁ ω)).Nonempty) ∧
    expect2 (fun ω : Sample2 n b T =>
        ‖NesterovFB.Rates.gradMap (KatyushaNs.favg fi) P η (output2 gf P η b x₁ ω)‖ ^ 2)
      ≤ expect2 (fun ω : Sample2 n b T =>
        Metric.infDist 0 (subdiffF fi g (output2 gf P η b x₁ ω)) ^ 2) ∧
    expect2 (fun ω : Sample2 n b T =>
        Metric.infDist 0 (subdiffF fi g (output2 gf P η b x₁ ω)) ^ 2)
      ≤ 228 * (Lf + δ * Real.sqrt ((numBlocks n b : ℝ) / b))
          * (compositeObj fi g x₁ - compositeStar fi g).toReal / (5 * T) ∧
    ∀ ω : Sample2 n b T,
      (gradLog2 gf P η b x₁ ω).length ≤ n + 5 * b * T ∧
      (proxLog2 gf P η b x₁ ω).length = T := by sorry

end PrefixVR.Supplement
