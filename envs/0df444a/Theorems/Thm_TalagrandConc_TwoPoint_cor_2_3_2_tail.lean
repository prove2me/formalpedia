-- Prove2me | Theorems.Thm_TalagrandConc_TwoPoint_cor_2_3_2_tail
-- name    : TalagrandConc.TwoPoint.cor_2_3_2_tail
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:44:44.065043+00:00
-- url     : https://prove2.me/theorems/8bdcec63-99cd-4713-9220-b374ab52cf56
-- title:
--   Corollary 2.3.2, Eq. (2.3.5) — a Gaussian tail bound for the Hamming distance on a biased cube $\{0,1\}^N$
-- statement:
--   Let $\Omega=\{0,1\}$, let $\mu$ be the probability with $\mu(\{1\})=p$, let $P=\mu^N$ on $\Omega^N$, and let $f(A,x)$ be the Hamming distance from $x\in\Omega^N$ to $A\subseteq\Omega^N$.
--
--   There is a universal constant $K>0$ with the following property. Let $0<p<1$, $N\ge 1$, and let $A\subseteq\Omega^N$ with $P(A)>0$. For every real $k$ with
--   $$\Big(4p(1-p)N\log\frac{1}{P(A)}\Big)^{1/2}\le k\le p(1-p)N$$
--   we have
--   $$P(\{f(A,x)\ge k\})\le\exp\Big(-\frac{1}{2p(1-p)N}\Big(k-\sqrt{2p(1-p)N\log\frac{1}{P(A)}}\Big)^2+\frac{Kk^3}{(p(1-p))^3N^2}\Big).$$
--
--   Up to the cubic correction this is the tail of a Gaussian with variance $p(1-p)N$, shifted by $\sqrt{2p(1-p)N\log(1/P(A))}$. The paper compares it with the optimal isoperimetric inequalities for hereditary sets: it is of essentially the same quality but holds for every set $A$.
--
--   **Formalization Note** $K$ is quantified before every other object. The hypotheses $0<p<1$, $N\ge 1$ and $P(A)>0$ are those under which the displayed formula is defined (it divides by $p(1-p)N$ and uses $\log(1/P(A))$). The $K$ here is independent of the $K$ in Eq. (2.3.4), following the paper's convention that $K$ denotes a universal constant that may change at each occurrence.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 89, Corollary 2.3.2, Eq. (2.3.5)

import Mathlib
import Definitions.Def_TalagrandConc_TwoPoint_Basic

open MeasureTheory
open scoped ENNReal NNReal

namespace TalagrandConc.TwoPoint

/-- Talagrand (1995), Corollary 2.3.2, Eq. (2.3.5), p. 89. There is a universal constant
`K` such that for `0 < p < 1`, `N ≥ 1`, `A ⊆ {0,1}^N` with `P(A) > 0`, and
`(4p(1-p)N log(1/P(A)))^{1/2} ≤ k ≤ p(1-p)N`,
`P(f(A,x) ≥ k) ≤ exp(-(k - (2p(1-p)N log(1/P(A)))^{1/2})² / (2p(1-p)N) + K k³/((p(1-p))³N²))`.
The hypotheses `0 < p < 1`, `N ≥ 1`, `P(A) > 0` are the conditions under which the page's
formula is defined (it divides by `p(1-p)N` and takes `log(1/P(A))`). -/
theorem cor_2_3_2_tail :
    ∃ K : ℝ, 0 < K ∧ ∀ (p : unitInterval), 0 < (p : ℝ) → (p : ℝ) < 1 →
      ∀ (N : ℕ), 0 < N → ∀ (A : Set (Fin N → Bool)), 0 < productMeasure N p A →
      ∀ k : ℝ,
        Real.sqrt (4 * (p : ℝ) * (1 - p) * N * Real.log (1 / (productMeasure N p A).toReal)) ≤ k →
        k ≤ (p : ℝ) * (1 - p) * N →
        productMeasure N p {x | ENNReal.ofReal k ≤ hammingDistToSet A x}
          ≤ ENNReal.ofReal (Real.exp (-(1 / (2 * (p : ℝ) * (1 - p) * N)) *
                (k - Real.sqrt (2 * (p : ℝ) * (1 - p) * N *
                  Real.log (1 / (productMeasure N p A).toReal))) ^ 2
              + K * k ^ 3 / (((p : ℝ) * (1 - p)) ^ 3 * N ^ 2))) := by sorry

end TalagrandConc.TwoPoint
