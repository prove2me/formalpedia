-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P01_remark13_oneShot
-- name    : QAlgorithms.Papers.Independent.Bridge50.P01.remark13_oneShot
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:35:25.22803+00:00
-- url     : https://prove2.me/theorems/1536a4ec-406b-4139-9a94-479d38694217
-- title:
--   Alternative one-shot EAC achievability penalty
-- statement:
--   Let $\mathcal N:A\to B$ be a finite-dimensional CPTP channel on nonzero spaces, and let $A'\simeq A$. Choose separate complete orthogonal local decompositions $\mathcal H_A=\bigoplus_t\mathcal H_A^t$ and $\mathcal H_{A'}=\bigoplus_t\mathcal H_{A'}^t$ with equal positive dimensions in each matched pair. Let $p(t)$ be a probability law and $|\Phi^t\rangle$ a maximally entangled unit vector on the matched pair. Define $|\vartheta\rangle=\sum_t\sqrt{p(t)}|\Phi^t\rangle$, $\vartheta=|\vartheta\rangle\langle\vartheta|$, $\pi_A^t$ and $\pi_{A'}^t$ as the normalized block projectors, and $\kappa=\sum_t p(t)\pi_A^t\otimes\pi_{A'}^t$. Write $\mathcal N\otimes{\rm id}$ explicitly on bipartite operators. Coding uses uniform messages, arbitrary finite prior entanglement, local CPTP encoders, one channel application, and a joint receiver POVM; its error is average decoding error. Hypothesis-testing entropy is the negative base-two logarithm of the minimum type-II test error at type-I error at most its superscript, with value $+\infty$ at zero.
--
--   For $0<\varepsilon<1$ and $0<\delta<\varepsilon$,
--
--   $$
--   \log_2 M_{\rm ea}^*(\mathcal N,\varepsilon)\ge D_H^{\varepsilon-\delta}\!\left((\mathcal N\otimes{\rm id})(\vartheta)\,\middle\Vert\,\sum_t p(t)\mathcal N(\pi_A^t)\otimes\pi_{A'}^t\right)-\log_2\frac{4\varepsilon}{\delta^2}.
--   $$
--
--   This gives the alternative one-shot bound with the error shift and penalty specific to Remark 13.
--
--   **Formalization Note** The same proof-used local correction to (4.16) is retained.
-- source:
--   On the Second-Order Asymptotics for Entanglement-Assisted Communication, arXiv:1405.1797v2, PDF p. 12, Remark 13, (4.46)

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P01

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P01

open QAlgorithms Filter MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

-- Reuse pinned accepted definitions; these are not other draft chunks.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P58 (testingBeta testingD)

open QAlgorithms.Papers.Independent.Information100.P63 (normalCDF normalQuantile)

open QAlgorithms.Papers.Independent.Information100.P71 (channelPower)

open QAlgorithms.Papers.Independent.Information100.P80 (log2)

open QAlgorithms.Papers.Independent.Dependency50.P19 (mutualInformation)

open QAlgorithms.Papers.Independent.Dependency50.P24 (cqState)

open QAlgorithms.Papers.Independent.Dependency50.P36 (relativeEntropyFinite)

open QAlgorithms.Papers.Independent.Frontier30.P01 (classicalState)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.12, Remark 13, Eq.(4.46): alternative one-shot penalty and error
shift. The proof-used local interpretation of (4.16) is as in Proposition 11. -/
theorem remark13_oneShot
    {A B : Type} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    [DecidableEq A] [DecidableEq B] (N : Superop A B) (hN : IsChannel N)
    (epsilon delta : ℝ) (h0 : 0 < epsilon) (h1 : epsilon < 1)
    (hd0 : 0 < delta) (hd1 : delta < epsilon) (R : BlockResource A) :
    testingD (epsilon - delta) (tensorIdentity N (blockTheta R))
      (∑ t, (R.weight t : ℂ) • Matrix.kronecker
        (N (blockMixed R R.leftBasis t)) (blockMixed R R.rightBasis t)) -
        (log2 (4 * epsilon / delta ^ 2) : EReal) ≤
      (codingBits N epsilon : EReal) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P01

end
