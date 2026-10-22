-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P41_tilted_law_minimizes_KL_on_level
-- name    : QAlgorithms.Papers.Independent.Gap48.P41.tilted_law_minimizes_KL_on_level
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:33:29.62892+00:00
-- url     : https://prove2.me/theorems/41c121ee-9b96-4d2e-b460-0a828309448d
-- title:
--   Tilted law minimizes KL on its alternative-divergence level set
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
--   Let $s>0$ satisfy $D(p(s)\Vert q)=r$. For every probability distribution $\widehat p$ on $X$,
--   $$
--   D(\widehat p\Vert q)=D(p(s)\Vert q)
--   \quad\Longrightarrow\quad
--   D(\widehat p\Vert p)\ge D(p(s)\Vert p).
--   $$
--   This is the Appendix's level-set minimization claim. Trial distributions need not be supported on $p$; their divergence to $p$ is then infinite.
-- source:
--   Strong Converse and Stein's Lemma in the Quantum Hypothesis Testing, arXiv:quant-ph/9906090v1, PDF p. 8, Appendix, (23): tilted law minimizes KL on a divergence level set

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

/-- PDF pp.8--9, Appendix, (23): every law on the tilt's q-divergence level has
at least the tilt's divergence to p. The comparison is between KL values; phat
is arbitrary and may have infinite divergence to p. No auxiliary t>=0 from the
source's proof is assumed. -/
theorem tilted_law_minimizes_KL_on_level [Nonempty X]
    (p q : X → ℝ) (hp : IsLaw p) (hq : IsLaw q) (r s : ℝ)
    (hr : classicalD (.finite 1 (by norm_num)) p q < (r : EReal)) (hs : 0 < s)
    (hlevel : classicalD (.finite 1 (by norm_num)) (tilt p q s) q = (r : EReal))
    (phat : X → ℝ) (hphat : IsLaw phat)
    (heq : classicalD (.finite 1 (by norm_num)) phat q = classicalD (.finite 1 (by norm_num)) (tilt p q s) q) :
    classicalD (.finite 1 (by norm_num)) (tilt p q s) p ≤ classicalD (.finite 1 (by norm_num)) phat p := by sorry

end QAlgorithms.Papers.Independent.Gap48.P41

end
