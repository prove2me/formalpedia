-- Prove2me | Theorems.Thm_TarskiQuasiFPT_UpperBound_Supplement_lemma_17
-- name    : TarskiQuasiFPT.UpperBound.Supplement.lemma_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:31:56.753303+00:00
-- url     : https://prove2.me/theorems/f93a437e-9856-485b-9ec3-efabec540ec5
-- title:
--   Lemma 17 — amplification: depth $q\log m/64$ succeeds on $\mathrm{Amp}_m(\mathcal H)$ w.p. at most $1/\sqrt m+q\varepsilon/3$
-- statement:
--   This is the §3.2 setting. $\mathcal H$ is a distribution whose support consists of monotone maps $H:[n]^k\to[n]^k$, each with a unique fixed point, and $m\ge1$. Let $q\ge0$ and $\varepsilon$ be reals satisfying the **induction hypothesis**: every deterministic decision tree of depth at most $q$ finds the fixed point of $H\sim\mathcal H$ with probability at most $\varepsilon$.
--
--   Then every deterministic decision tree of depth at most $q'=q\log m/64$ finds the fixed point of $F\sim\mathrm{Amp}_m(\mathcal H)$ with probability at most
--   $$\varepsilon'=\frac1{\sqrt m}+\frac{q\varepsilon}3.$$
--
--   This is the step that raises the lower bound by a $\Theta(\log m)$ factor per level in the proof of Theorem 6.
--
--   **Formalization Note** $q$, $q'$ and $\varepsilon$ are reals, and $\log$ is base two. Depth at most $q$ means at most $q$ queries on every oracle. The trees in the hypothesis act on $[n]^k$, and those in the conclusion act on $[m]^2\times[mn]^{4k}$.
--
--   Differences from the source:
--   - encoding: [n] = {1,…,n}, points of [n]^k ordered coordinatewise → Point n k = Fin k → Fin n (0-based values) with the pointwise order; reason: shift by one; same order, same instances
--   - encoding: [m]^2 × [mn]^{4k} with W = (a, b, X, Y), ordered coordinatewise → AmpPoint m n k = Fin m × Fin m × (Point (m*n) k × Point (m*n) k) × (Point (m*n) k × Point (m*n) k) with the product order; reason: the product order is the coordinatewise order of the concatenated vector; 0-based values
--   - encoding: S_{H,c}(X) = c at X = (P_H, P̄_H) → signFn returns c when H X.1 = X.1 and X.2 = complement X.1; reason: identical point when H has a unique fixed point P_H, which every H in the support has (§3.2 setting)
--   - encoding: a distribution of functions → PMF over functions; reason: the function spaces are finite, so every distribution is a PMF
--   - encoding: deterministic decision tree of depth at most q → DepthLE T q: T.queries g ≤ q for every oracle g (q real); reason: depth is the longest root-to-leaf path; the real bound is the paper's real expression
--   - reading: the tree "finds the fixed point" of F → the output T.eval F is a fixed point of F; reason: §3 uses "finds" for the output; for a lower bound this is the stronger of the two readings (a tree that queried the fixed point can output it at no extra depth)
--   - encoding: log (base two, footnote 1) → Real.logb 2; reason: the paper's convention
--   - encoding: m the base side-length of Amp_m, t* uniform on [m] → [NeZero m]; reason: uniform on [m] is undefined for m = 0; excludes only the undefined case
--   - encoding: q a depth bound → q : ℝ with 0 ≤ q; reason: a depth bound is nonnegative; the paper's q = q_{ℓ−1,m} is a nonnegative real
--   - generalization: §3.4 context of Lemma 17 (proof of Theorem 6): m ≥ 200 and H the level-(ℓ−1) distribution F_{ℓ−1,m} → any m ≥ 1 and any distribution D whose support consists of monotone maps with a unique fixed point (the §3.2 setting) satisfying the induction hypothesis; reason: the lemma's own statement assumes only the induction hypothesis for H, and the paper's proof uses nothing else (log m > 0 for m ≥ 2; at m = 1 the bound is ≥ 1); it specializes to the source at m ≥ 200, D = F_{ℓ−1,m}
-- source:
--   Chen, Gao, Li, Rubinstein, Yannakakis, Tarski Fixed Points in Quasi-FPT Queries, STOC 2027 submission #403 (October 2026), SHA-256 6a2841836f544481cc4548db5ea0222917f43c713b7a292c9947be9c149b9cd6, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/403.pdf, Lemma 17, PDF p. 23 (printed p. 22), with the induction hypothesis stated on PDF p. 22 (printed p. 21)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_TarskiQuasiFPT_UpperBound_Grid
import Definitions.Def_TarskiQuasiFPT_UpperBound_Supplement_LowerBound

open QAlgorithms
set_option autoImplicit false

namespace TarskiQuasiFPT.UpperBound.Supplement

/-- Lemma 17, PDF p. 23 (with the induction hypothesis of PDF p. 22). §3.2 setting: `D` is a
distribution whose support consists of monotone maps `[n]^k → [n]^k` with a unique fixed point,
and `m ≥ 1`. Let `q ≥ 0` and `ε` be reals such that every deterministic decision tree of depth at
most `q` finds the fixed point of `H ∼ D` with probability at most `ε`. Then every deterministic
decision tree of depth at most `q′ = q·log₂ m / 64` finds the fixed point of `F ∼ Amp_m(D)` with
probability at most `ε′ = 1/√m + qε/3`. -/
theorem lemma_17 {n k m : ℕ} [NeZero m] (D : PMF (Point n k → Point n k))
    (hD : ∀ H ∈ D.support, Monotone H ∧ HasUniqueFixedPoint H)
    (q ε : ℝ) (hq : 0 ≤ q)
    (hind : ∀ T : DecisionTree (Point n k) (Point n k) (Point n k),
      DepthLE T q → succProb D T ≤ ε) :
    ∀ T : DecisionTree (AmpPoint m n k) (AmpPoint m n k) (AmpPoint m n k),
      DepthLE T (q * Real.logb 2 m / 64) →
        succProb (ampDist m D) T ≤ 1 / Real.sqrt m + q * ε / 3 := by sorry

end TarskiQuasiFPT.UpperBound.Supplement
