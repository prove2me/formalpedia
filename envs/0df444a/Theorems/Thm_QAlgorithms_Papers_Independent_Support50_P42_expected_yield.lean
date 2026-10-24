-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P42_expected_yield
-- name    : QAlgorithms.Papers.Independent.Support50.P42.expected_yield
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T22:15:31.904246+00:00
-- url     : https://prove2.me/theorems/77d405cc-9cc3-4c14-b1c7-72373127467f
-- title:
--   Expected projected entropy and asymptotic unit efficiency
-- statement:
--   For a common Schmidt bias $p\in[0,1]$, let $p_{n,k}=\binom nk(1-p)^{n-k}p^k$, let $h_2(p)$ denote binary entropy in bits, and let $H(K)$ be the entropy of this binomial law. The expected concentrated entropy before standardization is
--
--   $$Y(n,p)=\sum_{k=0}^{n}p_{n,k}\log_2\binom nk,\qquad Y(n,p)+H(K)=nh_2(p).$$
--
--   For every $n\ge0$, $nh_2(p)-\log_2(n+1)\le Y(n,p)\le nh_2(p)$. If $0<p<1$, then $Y(n,p)/(nh_2(p))\to1$ along positive $n$. At $p=0$ or $1$, the yield is zero for all $n$. The added endpoint terms have logarithm $\log_2 1=0$. This gives the exact entropy loss and its asymptotically negligible fraction.
-- source:
--   Concentrating Partial Entanglement by Local Operations, arXiv:quant-ph/9511030v1, PDF p. 8, §III, Eq.(8): expected concentrated entropy and unit efficiency

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P42

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P42

open scoped BigOperators Matrix ComplexConjugate

open MeasureTheory ProbabilityTheory

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the exact accepted objects, without introducing same-name aliases.

open Information100.P21 (Op Vec FiniteLOCC)

open Dependency50.P42 (dimensionedPower singlets)

open Dependency50.P48 (pureFidelity)

open Gap48.P32 (pairOfState)

open Next46.P39 (rectAct)

/-- PDF p.8, Eq.(8), and p.4: expected projected entropy, exact entropy-loss
identity, logarithmic loss, and relative unit efficiency only when E>0.
The k=0,n terms added to the printed sum have log-rank zero. -/
theorem expected_yield (p : ℝ) (hp : 0≤p) (hp1 : p≤1) :
    (∀ n : ℕ, projectedYield n p+
      outcomeEntropy (fun k : Fin (n+1) => schmidtOutcomeWeight n p k.val)=(n : ℝ)*binEntropy2 p) ∧
    (∀ n : ℕ, (n : ℝ)*binEntropy2 p-Real.logb 2 (n+1 : ℕ)≤projectedYield n p ∧
      projectedYield n p≤(n : ℝ)*binEntropy2 p) ∧
    (0<p → p<1 → Filter.Tendsto
      (fun n : ℕ => projectedYield (n+1) p/(((n+1 : ℕ) : ℝ)*binEntropy2 p))
        Filter.atTop (nhds (1 : ℝ))) ∧
    (∀ n : ℕ, projectedYield n 0=0 ∧ projectedYield n 1=0) := by sorry

end QAlgorithms.Papers.Independent.Support50.P42

end
