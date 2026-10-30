-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P16_uniform_entropy_limit
-- name    : QAlgorithms.Papers.Independent.Advance50.P16.uniform_entropy_limit
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:27:55.620606+00:00
-- url     : https://prove2.me/theorems/afa2879c-daeb-4b08-9b86-6d96b48002c4
-- title:
--   Lemma 1: uniform entropy limit
-- statement:
--   Fix nonzero finite dimensions $d,n$. For every density matrix $\gamma$ on $\mathbb C^d\otimes\mathbb C^n$, put $\gamma_1=\operatorname{Tr}_2\gamma$ and $R(p,\gamma)=\operatorname{Tr}\gamma^p/\operatorname{Tr}\gamma_1^p$. The denominator is positive for $p>1$. The quotient $u=(1-R)/(p-1)$ extends continuously to $[1,\infty)$, with
--
--   $$u(1,\gamma)=-\left.\frac{d}{dp}R(p,\gamma)\right|_{p=1}=S(\gamma)-S(\gamma_1).$$
--
--   There is a finite constant $C\ge0$, depending only on $d,n$, such that $|u(p,\gamma)|\le C$ for every density $\gamma$ and $1\le p\le2$. For every $\epsilon>0$ there is $\delta>0$, independent of $\gamma$, such that $1\le p\le2$ and $|p-1|<\delta$ imply $|u(p,\gamma)-u(1,\gamma)|<\epsilon$. Here all entropies use natural logarithms. These uniform statements permit passage between the entropy limit and optimization over inputs.
-- source:
--   Multiplicativity of completely bounded p-norms implies a new additivity result, arXiv:quant-ph/0506196v2, PDF p. 6, Lemma 1: uniform entropy limit

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P16

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Topology

open Filter Set

namespace QAlgorithms.Papers.Independent.Advance50.P16

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact frozen counterparts; their bodies and conventions were checked for this repair.

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Dependency50.P19 (flip)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P30 (tensorMap)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P08 (depolarizing)

open QAlgorithms.Papers.Independent.Support50.P11 (wernerHolevoChannel)

/-- Lemma 1, PDF pp.6–7: full continuity, derivative identity, boundedness,
and continuity uniform over the density simplex. Constants follow the fixed dimensions. -/
theorem uniform_entropy_limit {D I : Type} [Fintype D] [Fintype I]
    [Nonempty D] [Nonempty I] :
    (∀ X : Mat (D × I), IsDensityMatrix X →
      (∀ p : ℝ, 1 < p → 0 < finiteTracePower (traceRight X) p) ∧
      ContinuousOn (fun p => uniformEntropyQuotient p X) (Ici 1) ∧
      uniformEntropyQuotient 1 X = entropy X - entropy (traceRight X) ∧
      HasDerivAt (powerRatio X) (entropy (traceRight X) - entropy X) 1) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ X : Mat (D × I), IsDensityMatrix X →
      ∀ p ∈ Icc (1 : ℝ) 2, |uniformEntropyQuotient p X| ≤ C) ∧
    (∀ epsilon : ℝ, 0 < epsilon → ∃ delta : ℝ, 0 < delta ∧
      ∀ X : Mat (D × I), IsDensityMatrix X → ∀ p ∈ Icc (1 : ℝ) 2,
        |p-1| < delta → |uniformEntropyQuotient p X - (entropy X - entropy (traceRight X))| < epsilon) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P16

end
