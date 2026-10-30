-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P20_example_comparison
-- name    : QAlgorithms.Papers.Independent.Bridge50.P20.example_comparison
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:08:03.844961+00:00
-- url     : https://prove2.me/theorems/fc70455a-1f49-405d-967c-a7487a00d3b3
-- title:
--   Exact substituted advantage for the dephasing and damping example
-- statement:
--   Let $k\ge0$ be an integer counting dephasing links, let $x,\lambda\in[0,1]$, and let $m>0$ be their common expected use count, including the one amplitude-damping link. With binary entropy $h(y)=-y\log_2y-(1-y)\log_2(1-y)$ and $0\log_20=0$, define
--
--   $$
--   s(x)=h\!\left(\sqrt{\frac x2(1-\frac x2)}+\frac12\right),\quad
--   t(\lambda)=h(\tfrac12-\tfrac\lambda4)-h(1-\tfrac\lambda4),\quad
--   r(x)=1-h(x/2),\quad v(\lambda)=\log_2(2-\lambda).
--   $$
--
--   The two substituted cut costs are $A=m[ks(x)+t(\lambda)]$ and $B=m[kr(x)+v(\lambda)]$. If $k[s(x)+r(x)]+t(\lambda)+v(\lambda)>0$, then
--
--   $$
--   \widetilde\mu=\frac{A-B}{A+B}=\frac{k[s(x)-r(x)]+t(\lambda)-v(\lambda)}{k[s(x)+r(x)]+t(\lambda)+v(\lambda)}.
--   $$
--
--   Here $s,t$ are the cited upper bounds on squashed entanglement, not its exact value. This is an exact scalar identity for the substituted comparison, with the common positive use count cancelled.
-- source:
--   Versatile relative entropy bounds for quantum networks, arXiv:1707.05543v2, PDF p. 20, §VI, (62)–(64): analytic expression for the example advantage

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P20

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P20

open QAlgorithms QAlgorithms.Entanglement

-- Reuse pinned accepted definitions; source-specific conventions are audited below.

open QAlgorithms.Papers.Independent.Dependency50.P35 (maxRelative)

open QAlgorithms.Papers.Independent.Information100.P04 (bellProjector)

open QAlgorithms.Papers.Independent.Information100.P53 (amplitudeDamping)

open QAlgorithms.Papers.Independent.Information100.P75 (mixedIdentity)

open QAlgorithms.Papers.Independent.Next46.P29 (zRotation)

open QAlgorithms.Papers.Independent.Support50.P11 (choiState)

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arXiv:1707.05543v2, PDF pp.20-21, (62)-(64): the exact substituted cost
ratio for k dephasing links and one amplitude-damping link. Positive common
expected use m cancels. The denominator is positive; no E_sq identity is asserted. -/
theorem example_comparison (k : ℕ) (x lambda m : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hl : lambda ∈ Set.Icc (0 : ℝ) 1)
    (hm : 0 < m)
    (hden : 0 < (k : ℝ) * (dephasingSquashedBound x + dephasingRelativeValue x) +
      (dampingSquashedBound lambda + amplitudeValue lambda)) :
    exampleAdvantage k x lambda m =
      ((k : ℝ) * (dephasingSquashedBound x - dephasingRelativeValue x) +
        (dampingSquashedBound lambda - amplitudeValue lambda)) /
      ((k : ℝ) * (dephasingSquashedBound x + dephasingRelativeValue x) +
        (dampingSquashedBound lambda + amplitudeValue lambda)) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P20

end
