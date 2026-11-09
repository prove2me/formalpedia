-- Prove2me | Theorems.Thm_TriFormQ_theorem_6
-- name    : TriFormQ.theorem_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:58:06.656471+00:00
-- url     : https://prove2.me/theorems/585d67d8-6ede-4e14-a734-253f3c3c6d54
-- title:
--   Theorem 6: a good base point with $O_q(\rho^2\lambda(\delta))$ quantum queries (corrected: query factor $\max\{1,\log_2(1/\delta)\}$)
-- statement:
--   Let $\mathbb F_q$ be a finite field. There is a constant $C$ (depending only on $q$) such that for every $n$, every $\rho$ and every failure parameter $\delta>0$ there is a randomized quantum query algorithm, depending on $n,\rho,\delta$ only, with the following property. For every trilinear form $f$ on $\mathbb F_q^n$ with $\mathrm{AR}(f)\le\rho$, given the evaluation oracle of $f$, the algorithm
--
--   1. makes at most $C\,\rho^2\,\lambda(\delta)$ queries on every run, where $\lambda(\delta)=\max\{1,\log_2(1/\delta)\}$, and
--   2. returns a good base point $v_0\in G$ with probability at least $1-\delta$.
--
--   This is the first step of Stage 2: the good fiber $Z_{v_0}$ is a large subspace on which the slices of $f$ have small rank.
--
--   Differences from the source:
--   - correction: $O_q(\rho^2\log(1/\delta))$ for any $\delta>0$ → $C\rho^2\max\{1,\log_2(1/\delta)\}$; reason: the printed bound is false as $\delta\to1$; over $\mathbb F_2$ take $f=\sum_{i\le r}u_iv_iw_i$ on $\mathbb F_2^r$, so $\mathrm{AR}(f)=r\log_2(4/3)=:\rho$, $\mathrm{rk} f\langle v\rangle=\mathrm{wt}(v)$, $M(v)=(3/2)^{r-\mathrm{wt}(v)}$, so $G\subseteq\{v:\mathrm{wt}(v)\le r\log_2(4/3)+3\}$ (from $2^{\mathrm{wt}(v)}\le8\cdot2^{\mathrm{AR}}$), of density $\varepsilon_r\le2^{-0.02r}$ for large $r$ since $1-H_2(\log_2(4/3))>0.0209$, and $0\notin G$ since $(3/2)^r>8(4/3)^r$; with $1-\delta=2\varepsilon_r$ the printed bound $C\rho^2\log_2(1/\delta)$ is below one query for large $r$, and a 0-query algorithm has a fixed output law $D$, so for some invertible $P$ the form $f(u,Pv,w)$ (same AR, good set $P^{-1}G$) has $D(P^{-1}G)\le|G|/(2^r-1)<1-\delta$; identical for $\delta\le1/2$
--   - encoding: we are given an upper bound $\rho\ge\mathrm{AR}(f)$ → the algorithm takes $\rho$ as input and the guarantee holds for every $f$ with $\mathrm{AR}(f)\le\rho$; reason: the algorithm is chosen before the oracle
--   - encoding: randomized quantum query algorithm making at most $X$ queries → an `AdaptiveAlg` (rounds of the platform's `QueryAlg` against the standard oracle, full measurement, classical choice of the next round) chosen before the oracle, whose worst-case query count over positive-probability runs on that oracle is at most $X$; reason: platform query model; classical coins are 0-query rounds and offline computation on explicit data is free, as in the paper
-- source:
--   Grigorescu–Juba–Wimmer–Xie, Optimal Quantum Query Bounds for Identifying Classes of 3-Tensors, STOC 2027 submission (manuscript sha256 c56b0365…), Theorem 6, p.29 (PDF p.32)

import Definitions.Def_TriFormQ_oracle
import Definitions.Def_TriFormQ_AdaptiveAlg_outProb
import Definitions.Def_TriFormQ_AdaptiveAlg_maxQueries
import Definitions.Def_TriFormQ_lam
import Definitions.Def_TriFormQ_goodSet

namespace TriFormQ

/-- Grigorescu–Juba–Wimmer–Xie, *Optimal Quantum Query Bounds for Identifying Classes of
3-Tensors*, STOC 2027 submission (manuscript sha256 c56b0365…), Theorem 6, p.29 (PDF p.32): "Let
f : U × V × W → 𝔽_q be a trilinear form where U, V, W are n-dimensional vector spaces over 𝔽_q.
Suppose we are given an upper bound ρ ≥ AR(f). Then for any failure parameter δ > 0, there is a
randomized quantum query algorithm which, with probability at least 1 − δ return a good base
point v₀ ∈ G. The query complexity of the algorithm is at most O_q(ρ² log(1/δ))."

**Formalization Note.** The algorithm is given `n`, `ρ` and `δ` and is chosen before the oracle;
the guarantee holds for every form with `AR(f) ≤ ρ`. The constant `C` depends only on the field.
Correction: `log(1/δ)` is replaced by `λ(δ) = max{1, log₂(1/δ)}`; the printed
bound is false as `δ → 1` (see the item's differences). -/
theorem theorem_6 {F : Type} [Field F] [Fintype F] [DecidableEq F] :
    ∃ C : ℝ, ∀ (n : ℕ) (ρ δ : ℝ), 0 < δ →
      ∃ A : AdaptiveAlg (Vec F n × Vec F n × Vec F n) F (Vec F n), ∀ θ : TriForm F n,
        AR θ ≤ ρ →
          (A.maxQueries (oracle θ) : ℝ) ≤ C * ρ ^ 2 * lam δ ∧
          1 - δ ≤ A.outProb (oracle θ) (fun v => v ∈ goodSet θ) := by sorry

end TriFormQ
