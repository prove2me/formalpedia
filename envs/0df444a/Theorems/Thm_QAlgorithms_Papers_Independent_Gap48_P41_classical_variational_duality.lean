-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P41_classical_variational_duality
-- name    : QAlgorithms.Papers.Independent.Gap48.P41.classical_variational_duality
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:31:41.555093+00:00
-- url     : https://prove2.me/theorems/ae248ff7-e79d-439c-9dc9-965780e242e5
-- title:
--   Classical variational duality with attained tilted minimizer
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
--   Suppose there is a finite $t>0$ such that $D(p(t)\Vert q)=r$. Then $p(t)$ is a probability law, it attains the variational minimum, and $t$ attains the noncompact maximum:
--   $$
--   \widetilde u(r)=D(p(t)\Vert p)=g_r(t)=\max_{s\ge0}g_r(s).
--   $$
--   Writing $\eta(t)=\sum_{j:p_j>0}p(t)_j\log(p_j/q_j)$, the parametrization is
--   $$
--   \widetilde u(r)=t\eta(t)-\widetilde\psi(t),\qquad r=(1+t)\eta(t)-\widetilde\psi(t).
--   $$
--   This states the paper's active-rate duality. The finite positive tilt premise is its precise Appendix condition for the main text's phrase “not so large”.
-- source:
--   Strong Converse and Stein's Lemma in the Quantum Hypothesis Testing, arXiv:quant-ph/9906090v1, PDF p. 7, §5 and Appendix, (21): classical variational exponent and tilted minimizer

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

/-- PDF pp.7--9, (21) and Appendix: the active-rate classical duality, with
BOTH extrema attained at the constructed tilt and its parameter. The finite
positive tilt premise is exactly the source's precise meaning of 'not so large'.
The final two equations preserve the Appendix's parametrization. -/
theorem classical_variational_duality [Nonempty X]
    (p q : X → ℝ) (hp : IsLaw p) (hq : IsLaw q) (r t : ℝ)
    (hr : classicalD (.finite 1 (by norm_num)) p q < (r : EReal)) (ht : 0 < t)
    (hlevel : classicalD (.finite 1 (by norm_num)) (tilt p q t) q = (r : EReal)) :
    IsLaw (tilt p q t) ∧
    IsLeast (classicalValues p q r) (classicalD (.finite 1 (by norm_num)) (tilt p q t) p) ∧
    classicalMinimum p q r = classicalD (.finite 1 (by norm_num)) (tilt p q t) p ∧
    classicalMinimum p q r = (classicalG p q r t : EReal) ∧
    IsGreatest (classicalDualValues p q r) (classicalMinimum p q r) ∧
    classicalMinimum p q r = ((t * tiltedLogLikelihood p q t - classicalPsi p q t : ℝ) : EReal) ∧
    r = (1 + t) * tiltedLogLikelihood p q t - classicalPsi p q t := by sorry

end QAlgorithms.Papers.Independent.Gap48.P41

end
