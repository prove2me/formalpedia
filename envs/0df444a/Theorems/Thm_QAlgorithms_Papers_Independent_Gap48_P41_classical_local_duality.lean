-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P41_classical_local_duality
-- name    : QAlgorithms.Papers.Independent.Gap48.P41.classical_local_duality
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:32:16.931637+00:00
-- url     : https://prove2.me/theorems/45a7d31c-b5f9-4bf1-910d-394ee500f9ef
-- title:
--   Small-rate classical exponent agrees with the compact quantum formula
-- statement:
--   Let $X$ be a nonempty finite alphabet, and let $p,q$ be probability distributions on $X$, allowing zero coordinates. Write $D(a\Vert b)$ for natural-log Kullback–Leibler divergence, with zero mass contributing zero and support failure giving $+\infty$. For real $r>D(p\Vert q)$, put
--   $$
--   \widetilde\psi(s)=\log\sum_{j\in X}p_j^{1+s}q_j^{-s},\qquad
--   p(s)_j=e^{-\widetilde\psi(s)}p_j^{1+s}q_j^{-s},\qquad
--   g_r(s)=\frac{s r-\widetilde\psi(s)}{1+s}.
--   $$
--   A zero $p_j$ gives zero tilted mass, and inverse powers act only on positive support. The finite rate condition entails $\operatorname{supp}p\subseteq\operatorname{supp}q$. Define
--   $$
--   \widetilde u(r)=\inf_{\widehat p:\,D(\widehat p\Vert q)\le r}
--   \{D(\widehat p\Vert p)+r-D(\widehat p\Vert q)\},
--   $$
--   where the infimum ranges over all probability distributions. The second divergence is finite for every feasible law; the first may be infinite.
--
--   Suppose $0<t\le1$ and $D(p(t)\Vert q)=r$. Then
--   $$
--   \widetilde u(r)=g_r(t)=\max_{0\le s\le1}g_r(s),
--   $$
--   with the maximum attained at $t$. Equivalently, for diagonal density matrices $\rho=\operatorname{diag}(p_j)$ and $\sigma=\operatorname{diag}(q_j)$, this value equals $u(r)=\max_{0\le s\le1}\frac{sr-\log\operatorname{Tr}(\rho^{1+s}\sigma^{-s})}{1+s}$, the paper's compact Petz expression (15).
--
--   This pins the small-rate comparison by an explicit source-derived tilt condition and does not extend it to arbitrary rates.
-- source:
--   Strong Converse and Stein's Lemma in the Quantum Hypothesis Testing, arXiv:quant-ph/9906090v1, PDF p. 7, §5, unnumbered: small-rate classical exponent agrees with (15)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P41

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P41

open scoped Matrix ComplexOrder BigOperators

open Filter QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Information100.P07 (positiveProjection)

open QAlgorithms.Papers.Independent.Dependency50.P28
  (tr SupportLE relativeEntropy scalarPower classicalD typeI accept TestSequence
    scaled logNonnegativeExtended)

open QAlgorithms.Papers.Independent.Claimed50.P15 (legendre)

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I : Type} [Fintype I] [DecidableEq I]

variable {X : Type} [Fintype X]

/-- PDF pp.7--9: the small-rate classical exponent equals the compact [0,1]
formula, with an attained maximum. The source's vague 'sufficiently small' is
pinned by a matching tilt with 0<t<=1; the diagonal quantum comparison is explicit. -/
theorem classical_local_duality [Nonempty X] [DecidableEq X]
    (p q : X → ℝ) (hp : IsLaw p) (hq : IsLaw q) (r t : ℝ)
    (hr : classicalD (.finite 1 (by norm_num)) p q < (r : EReal)) (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hlevel : classicalD (.finite 1 (by norm_num)) (tilt p q t) q = (r : EReal)) :
    classicalMinimum p q r = (classicalG p q r t : EReal) ∧
    IsGreatest (classicalG p q r '' Set.Icc 0 1) (classicalG p q r t) ∧
    classicalMinimum p q r =
      (petzExponent (Matrix.diagonal (fun x => (p x : ℂ)))
        (Matrix.diagonal (fun x => (q x : ℂ))) r : EReal) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P41

end
