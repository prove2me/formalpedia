-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P30_deterministic_squeezing_reduction
-- name    : QAlgorithms.Papers.Independent.Gap48.P30.deterministic_squeezing_reduction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:23:15.125185+00:00
-- url     : https://prove2.me/theorems/b8f8ec40-3296-4555-95c1-03f64449e19a
-- title:
--   Appendix 5d: deterministic squeezing reduction for every Fock input
-- statement:
--   Let $k\ge0$ and $0\le\lambda'<\lambda<1$. There exists $0\le T<1$ with $\lambda'=\sqrt T\lambda$. If $\lambda'>0$, Bob first splits his mode with vacuum and counts $l$ reflected photons. He then performs the explicit $l$-photon decrement instrument at parameter $\lambda'$, with outcome $m$, and sends $(l,m)$ to Alice. Alice applies its complete shift extension, with local Kraus outcome $i$. Every local instrument is complete on the whole Fock space. If $v_{lmi}$ is the resulting terminal branch, then
--
--   $$
--   v_{lmi}=c_{lmi}|\Psi_{\lambda'}^{(k)}\rangle\quad\text{for every }(l,m,i)\in\mathbb N^3,\qquad
--   \sum_{l,m,i}\|v_{lmi}\|^2=1.
--   $$
--
--   All tensor operations realize their physical matrices, both input and target have norm one, and the countably many branch probabilities converge to total one. The zero decrement is the identity instrument. If $\lambda'=0$, independent complete local reset instruments prepare the product target $|k,0\rangle$; their terminal branches satisfy the same deterministic criterion.
--
--   Thus the specified adaptive countable LOCC protocol converts stronger to weaker squeezing for every Fock input. Its direction is the reverse of the corresponding probability-majorization arrow.
-- source:
--   Majorization theory approach to the Gaussian channel minimum entropy conjecture, arXiv:1111.1986v1, PDF p. 10, Appendix 5d, final paragraph

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P30

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P30

open Filter MeasureTheory

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- arXiv:1111.1986v1, PDF p.10, Appendix 5d final paragraph. Stronger to
weaker squeezing is achieved by the actual adaptive countable instrument:
Bob splits and counts ell, performs the ell-decrement, and sends (ell,m) to
Alice for her conditional shift. Zero target squeezing is independent local
product preparation. This does not use the defective printed R matrix. -/
theorem deterministic_squeezing_reduction (k : ℕ) (lambda target : ℝ)
    (ht : 0 ≤ target) (hlt : target < lambda) (hlu : lambda < 1) :
    ∃ T : ℝ, 0 ≤ T ∧ T < 1 ∧ target = Real.sqrt T * lambda ∧
      if target = 0 then ResetProtocol k (squeezed k lambda) (squeezed k target)
      else SqueezingReductionProtocol k lambda target T := by sorry

end QAlgorithms.Papers.Independent.Gap48.P30

end
