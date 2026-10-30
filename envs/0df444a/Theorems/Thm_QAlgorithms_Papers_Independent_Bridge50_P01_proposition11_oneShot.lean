-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P01_proposition11_oneShot
-- name    : QAlgorithms.Papers.Independent.Bridge50.P01.proposition11_oneShot
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:33:57.791889+00:00
-- url     : https://prove2.me/theorems/887ad219-45bf-4e05-a9b2-91d002278972
-- title:
--   One-shot EAC achievability from matched-block resources
-- statement:
--   Let $\mathcal N:A\to B$ be a finite-dimensional CPTP channel on nonzero spaces, and let $A'\simeq A$. Choose separate complete orthogonal local decompositions $\mathcal H_A=\bigoplus_t\mathcal H_A^t$ and $\mathcal H_{A'}=\bigoplus_t\mathcal H_{A'}^t$ with equal positive dimensions in each matched pair. Let $p(t)$ be a probability law and $|\Phi^t\rangle$ a maximally entangled unit vector on the matched pair. Define $|\vartheta\rangle=\sum_t\sqrt{p(t)}|\Phi^t\rangle$, $\vartheta=|\vartheta\rangle\langle\vartheta|$, $\pi_A^t$ and $\pi_{A'}^t$ as the normalized block projectors, and $\kappa=\sum_t p(t)\pi_A^t\otimes\pi_{A'}^t$. Write $\mathcal N\otimes{\rm id}$ explicitly on bipartite operators. Coding uses uniform messages, arbitrary finite prior entanglement, local CPTP encoders, one channel application, and a joint receiver POVM; its error is average decoding error. Hypothesis-testing entropy is the negative base-two logarithm of the minimum type-II test error at type-I error at most its superscript, with value $+\infty$ at zero.
--
--   For $0<\varepsilon<1$ and $0<\delta<\varepsilon/2$,
--
--   $$
--   \log_2 M_{\rm ea}^*(\mathcal N,\varepsilon)\ge
--   D_H^{\varepsilon-2\delta}((\mathcal N\otimes{\rm id})(\vartheta)\Vert(\mathcal N\otimes{\rm id})(\kappa))
--   -\log_2\frac{1-\varepsilon}{\delta^2}.
--   $$
--
--   This is the paper's one-shot bound used for its second-order achievability analysis.
--
--   **Formalization Note** The local decompositions are the proof-used correction of the dimensional error in (4.16); the entire tensor space also contains unmatched block pairs.
-- source:
--   On the Second-Order Asymptotics for Entanglement-Assisted Communication, arXiv:1405.1797v2, PDF p. 9, Proposition 11, (4.18)

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

/-- PDF p.9, Proposition 11, Eq.(4.18): one-shot bound for matched-block
resources. Source correction: replace the impossible full-tensor equality
(4.16) by the separate local decompositions used in its proof. -/
theorem proposition11_oneShot
    {A B : Type} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    [DecidableEq A] [DecidableEq B] (N : Superop A B) (hN : IsChannel N)
    (epsilon delta : ℝ) (h0 : 0 < epsilon) (h1 : epsilon < 1)
    (hd0 : 0 < delta) (hd1 : delta < epsilon / 2) (R : BlockResource A) :
    testingD (epsilon - 2 * delta)
      (tensorIdentity N (blockTheta R)) (tensorIdentity N (blockKappa R)) -
        (log2 ((1 - epsilon) / delta ^ 2) : EReal) ≤
      (codingBits N epsilon : EReal) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P01

end
