-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P49_epsilon_affineEnvelope_convex
-- name    : QAlgorithms.Papers.Independent.Information100.P49.epsilon_affineEnvelope_convex
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:48:41.772535+00:00
-- url     : https://prove2.me/theorems/9489e2f4-4dc8-4419-928c-8b6dc7cbd8e2
-- title:
--   Affine envelope and joint convexity of the moment-resolved entropy
-- statement:
--   Let $\tau\ne0$, $k=|\tau|$, $y>0$, $0<\xi\le1$, and $y\ge|1-\tau|$ be the canonical channel parameters. With natural logarithms and $0\ln0=0$, set $G(\mu)=g((\mu-1)/2)$, where $g(v)=(v+1)\ln(v+1)-v\ln v$. Define
--   $$h(z,w)=G\!\left(\sqrt{(kz+y/\xi)(kw+y\xi)}\right),\qquad \widehat u=\min\{z,\max\{1/w,1/\xi\}\},\qquad \varepsilon(z,w)=h(\widehat u,1/\widehat u).$$
--   For $z,w>0$ with $zw\ge1$, let $f(u)=h(u,1/u)$ and $q(v)=h(1/v,v)$. Then
--   $$\varepsilon(z,w)=\sup\left(\{G(k+y)\}\cup\{f(u)+f'(u)(z-u):0<u<1/\xi\}\cup\{q(v)+q'(v)(w-v):0<v<\xi\}\right).$$
--   The function $\varepsilon$ is jointly convex on this domain and nonincreasing in each coordinate. The derivatives are derivatives of the entire displayed one-variable compositions.
--
--   The envelope supplies the convexity used to control average signal entropy under arbitrary signal ensembles.
--
--   **Formalization Note** The supremum is taken in the extended reals and is asserted equal to the finite real value $\varepsilon(z,w)$. Thus an empty or unbounded real supremum cannot acquire a default value.
-- source:
--   Classical Capacity of Single-Mode Bosonic Gaussian Channels, arXiv:2610.22308v1, PDF p. 4, Eq. (18)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P49

namespace QAlgorithms.Papers.Independent.Information100.P49

open scoped BigOperators

/-- Eq. (18), PDF p.4: the exact affine envelope, joint convexity and
coordinatewise nonincrease of the moment-resolved entropy on its admissible domain. -/
theorem epsilon_affineEnvelope_convex (c : CanonicalParameters) :
    (∀ z w : ℝ, (z, w) ∈ momentDomain →
      (momentEntropy c z w : EReal) = sSup (affineEntropyValues c z w)) ∧
    ConvexOn ℝ momentDomain (fun q => momentEntropy c q.1 q.2) ∧
    (∀ z w z2 : ℝ, (z, w) ∈ momentDomain → z ≤ z2 →
      momentEntropy c z2 w ≤ momentEntropy c z w) ∧
    (∀ z w w2 : ℝ, (z, w) ∈ momentDomain → w ≤ w2 →
      momentEntropy c z w2 ≤ momentEntropy c z w) := by sorry

end QAlgorithms.Papers.Independent.Information100.P49
