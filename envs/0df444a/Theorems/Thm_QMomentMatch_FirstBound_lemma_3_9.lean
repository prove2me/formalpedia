-- Prove2me | Theorems.Thm_QMomentMatch_FirstBound_lemma_3_9
-- name    : QMomentMatch.FirstBound.lemma_3_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T19:00:58.243573+00:00
-- url     : https://prove2.me/theorems/de228695-5dc5-455c-8083-70617dec66ba
-- title:
--   Lemma 3.9 — Taylor approximation of $q_{\mathbf w}$: $\mathbb E|q_{\mathbf w}(Z)-Q_{\mathbf w}(Z)|\le\frac{2A^{r-1}}{(2r)!}\left(\frac{128T^2}{N}\right)^r$
-- statement:
--   Setting of §3.3: let $A\ge1$, let $\mathcal A$ be a quantum algorithm making $T$ standard queries to $f:[N]\to[N]$, with $N\ge\max\{8,4A\}$, $T\ge1$ and $T^2\le N/64$, and let $r\ge2$. Put $S=\{0\}\cup[A]$, $m=\lfloor N/2\rfloor$, $H=\lfloor N/4\rfloor$, $h(z)=\Pr_{f\sim\mathcal D_{\mathbf c(z)}}[\mathcal A^f=1]$ for $z\in S^m$ (with $\mathbf c(z)$ from step 2 of Definition 2.1), and for $w\in S^{m-1}$ let $w=\sum_iw_i$ and $q_w(s)=h(w,s)$.
--
--   For every $w\in S^{m-1}$ with $w\le 3N/4$, the function $q_w$ admits a polynomial extension of degree at most $2T$, $q_w(s)=\sum_{j=0}^{2T}a_{w,j}s^j$ for $s\in S$, with real coefficients and $|q_w(z)|\le1$ for every $z\in\{0\}\cup[H]$, such that every mean-one random variable $Z$ supported on $S$ satisfies
--   $$\mathbb E_Z\big[|q_w(Z)-Q_w(Z)|\big]\le\frac{2A^{r-1}}{(2r)!}\left(\frac{128T^2}{N}\right)^r,\qquad Q_w(z)=\sum_{j=0}^{\min\{r-1,2T\}}a_{w,j}z^j .$$
--
--   This is where the polynomial method (Lemma 3.1) and the Taylor bound (Lemma 3.2) combine: the single-coordinate acceptance function is approximated by its low-degree part, uniformly over mean-one laws.
--
--   **Formalization Note** The extension is an existentially chosen real polynomial $q$ with `natDegree q ≤ 2T`, fixed before $Z$; $Q_w$ is its truncation to degrees $\le\min\{r-1,2T\}$. A mean-one random variable on $S$ is a probability vector $p$ on `Fin (A + 1)` with $\sum_sp(s)s=1$, and the expectation is the finite sum.
--
--   Differences from the source:
--   - encoding: "making at most $T$ queries" → `QueryAlg … T` (exactly $T$ oracle calls); reason: Lemma 3.9 is applied with the algorithm's own number of queries, and the bound is increasing in $T$.
--   - encoding: $f:[N]\to[N]$ and its oracle → `f : Fin N → ZMod N` with `xorOracle f`; reason: 0-based domain and labels $j\mapsto j\bmod N$; the oracle is the same unitary.
--   - encoding: "mean-one random variable $Z$ supported on $S$" → probability vector $p$ on `Fin (A + 1)` with $\sum_sp(s)s=1$; reason: the expectation depends only on the law of $Z$.
--   - encoding: $S^{m-1}$ and $(w,s)$ → `Fin (N / 2 - 1) → S` and `appendLast w s`; reason: the source puts the varied coordinate last (p. 18).
-- source:
--   Chandrima Kayal, Frédéric Magniez, Sayantan Sen, Dániel Szabó, STOC 2027 submission #564 (October 2026), §3.3 standing setting p. 21, Lemma 3.9, pp. 21–22

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_QMomentMatch_FirstBound_Basic
import Definitions.Def_QMomentMatch_FirstBound_InducedDist

namespace QMomentMatch.FirstBound

open QAlgorithms Polynomial

/-- Lemma 3.9 (Taylor approximation), pp. 21–22, in the standing setting of §3.3: `A ≥ 1`,
`N ≥ max{8, 4A}`, `T ≥ 1`, `T² ≤ N/64`, `r ≥ 2`, `m = ⌊N/2⌋`, `H = ⌊N/4⌋`,
`h(z) = Pr_{f ∼ D_{c(z)}}[A^f = 1]`, `q_w(s) = h(w, s)`. -/
theorem lemma_3_9 (A N T r : ℕ) [NeZero N] (hA : 1 ≤ A) (hN8 : 8 ≤ N) (hNA : 4 * A ≤ N)
    (hT : 1 ≤ T) (hTN : (T : ℝ) ^ 2 ≤ (N : ℝ) / 64) (hr : 2 ≤ r)
    (W : Type*) [Fintype W] [DecidableEq W]
    (alg : QueryAlg (Fin N) (ZMod N) W T) (out : (Fin N × ZMod N) × W → Bool)
    (w : Fin (N / 2 - 1) → Fin (A + 1)) (hw : (∑ i, ((w i : ℕ) : ℝ)) ≤ 3 * (N : ℝ) / 4) :
    ∃ q : ℝ[X], q.natDegree ≤ 2 * T ∧
      (∀ s : Fin (A + 1), q.eval ((s : ℕ) : ℝ) = hAcc alg out (appendLast (m := N / 2) w s)) ∧
      (∀ z : ℕ, z ≤ N / 4 → |q.eval (z : ℝ)| ≤ 1) ∧
      ∀ p : Fin (A + 1) → ℝ, IsProbVec p → moment p 1 = 1 →
        ∑ s, p s * |q.eval ((s : ℕ) : ℝ) -
            (∑ j ∈ Finset.range (min (r - 1) (2 * T) + 1), C (q.coeff j) * X ^ j).eval
              ((s : ℕ) : ℝ)| ≤
          2 * (A : ℝ) ^ (r - 1) / ((2 * r).factorial : ℝ) * (128 * (T : ℝ) ^ 2 / N) ^ r := by sorry

end QMomentMatch.FirstBound
