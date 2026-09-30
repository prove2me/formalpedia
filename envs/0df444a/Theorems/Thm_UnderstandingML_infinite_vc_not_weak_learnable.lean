-- Prove2me | Theorems.Thm_UnderstandingML_infinite_vc_not_weak_learnable
-- name    : UnderstandingML.infinite_vc_not_weak_learnable
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T03:58:57.016974+00:00
-- url     : https://prove2.me/theorems/6018ba3c-51c1-4bd6-ba12-822a36283bb9
-- title:
--   §10.1: a class of infinite VC-dimension is not γ-weak-learnable for any γ > 0
-- statement:
--   **§10.1.** The fundamental theorem of learning (Theorem 6.8) states that if $H$ has VC-dimension $d$ then $m_H(\epsilon,\delta) \ge C_1 \frac{d + \log(1/\delta)}{\epsilon}$. Applying this with $\epsilon = 1/2 - \gamma$ we immediately obtain that if $d = \infty$ then $H$ is not γ-weak-learnable.
--
--   Formally (domain with measurable singletons, measurable hypotheses): if $\mathrm{VCdim}(H) = \infty$ and $\gamma > 0$ then `WeakLearnable H γ` fails.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §10.1 p. 132 (the remark after Definition 10.1; via Exercise 5.3 and Lemma B.1)

import Definitions.Def_UnderstandingML_Boosting

open MeasureTheory

namespace UnderstandingML

/-- **§10.1** (p. 132). If `VCdim(H) = ∞` then `H` is not γ-weak-learnable: from the statistical
perspective weak learnability is characterized by the VC-dimension, just as PAC learning is.
(Domain with measurable singletons, measurable hypotheses; the book derives this from the
lower bound of Theorem 6.8 at `ε = 1/2 − γ`, which needs the `km`-point form of the
No-Free-Lunch argument, Exercise 5.3, for `γ` close to `0`.) -/
theorem infinite_vc_not_weak_learnable {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] (H : Set (X → Bool)) (hH : ∀ h ∈ H, Measurable h)
    (hvc : vcDim H = ⊤) {γ : ℝ} (hγ : 0 < γ) : ¬ WeakLearnable H γ := by sorry

end UnderstandingML
