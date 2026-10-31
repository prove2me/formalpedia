-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P01_trine_nonpolytopic_eb_example
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P01.trine_nonpolytopic_eb_example
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:22:20.743597+00:00
-- url     : https://prove2.me/theorems/c5469e2e-48fb-4720-92cb-fbd28274df36
-- title:
--   A trine measurement has a nonpolytopic EB image
-- statement:
--   Put $\theta_j=2\pi j/3$ for $j=1,2,3$ and let $v_j=(\cos\theta_j,\sin\theta_j)\in\mathbb R^2\subset\mathbb C^2$, the real coordinates of powers of a primitive third root of unity. Set $M_j=(2/3)v_jv_j^*$ and define $T:M_2(\mathbb C)\to M_3(\mathbb C)$ by $T(A)=\sum_j\operatorname{Tr}(M_jA)e_je_j^*$ in the computational output basis. Then $T$ is CPTP and entanglement breaking, and
--   $$\operatorname{Im}T=\left\{\operatorname{diag}\left(\frac{1+a\cos(2\theta_j)+b\sin(2\theta_j)}3\right)_{j=1}^3:a,b\in\mathbb R,\ a^2+b^2\le1\right\}.$$
--   This filled circle in the diagonal trace-one plane is not a convex polytope.
--
--   Thus an entanglement-breaking channel need not have a polytopic image.
-- source:
--   Quantum channels with polytopic images and image additivity, arXiv:1408.2340v1, PDF p. 3, §2, unnumbered example (4): EB image need not be a polytope

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P01

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Intakenext100.P01

open QAlgorithms.Papers.Independent.Information100.P44 (Mat)

open QAlgorithms.Papers.Independent.Information100.P07 (projection)

open QAlgorithms.Papers.Independent.Dependency50.P23 (IsEB)

open QAlgorithms.Papers.Independent.Dependency50.P05 (renyiEntropy)

/-- §2, equation (4) and Figure 1, PDF pp.3–4: a CPTP entanglement-breaking example
with filled circular, nonpolytopic image. The primitive root is represented in real coordinates. -/
theorem trine_nonpolytopic_eb_example :
    IsChannel trineMap ∧ IsEB trineMap ∧ channelImage trineMap = trineCircle ∧
      ¬ IsPolytopic (channelImage trineMap) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P01

end
