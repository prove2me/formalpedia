-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P38_lemma7_oneShotDecoupling
-- name    : QAlgorithms.Papers.Independent.Gap48.P38.lemma7_oneShotDecoupling
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T05:08:57.363563+00:00
-- url     : https://prove2.me/theorems/795deb06-6919-4d8f-8465-9baca2b21d70
-- title:
--   Lemma 7 (One-shot decoupling [12])
-- statement:
--   Let $\varphi^{CE}$ be a density matrix on nonempty finite complex registers. Fix a unitary identification $W:C\to S\widehat B$, and for each unitary $U$ on $C$ define $\varphi_U=(WU\otimes I_E)\varphi(WU\otimes I_E)^\dagger$. With normalized Haar probability $dU$, the maximally mixed state $\pi^{\widehat B}=I_{\widehat B}/|\widehat B|$, and actual partial traces,
--
--   $$\int_{U(C)}\|\varphi_U^{\widehat BE}-\pi^{\widehat B}\otimes\varphi^E\|_1^2\,dU\le\frac{|C|\,\operatorname{rank}(\varphi^E)\,\|\varphi^{CE}\|_2^2}{|S|^2}.$$
--
--   The integrand is the square of the full trace norm; the right side uses the squared Hilbert–Schmidt norm. This is the one-shot decoupling estimate attributed to [12], with neither an extra marginal-purity subtraction nor an extra reference-dimension hypothesis.
-- source:
--   Optimal quantum source coding with quantum information at the encoder and decoder, arXiv:0706.2907v2, PDF p. 11, Lemma 7 (One-shot decoupling [12])

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P38

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Gap48.P38

/-- Lemma 7 (one-shot decoupling, attributed to [12]), PDF p.11, eq.(24).
The integrand is the SQUARE of the FULL trace norm, and the numerator is
|C| rank(phi_E) ||phi_CE||_2^2, with no subtracted marginal-purity term. -/
theorem lemma7_oneShotDecoupling
    (c s b e : ℕ) (hc : 0 < c) (hs : 0 < s) (hb : 0 < b) (he : 0 < e)
    (phi : Matrix (Fin c × Fin e) (Fin c × Fin e) ℂ)
    (hphi : IsDensityMatrix phi)
    (W : Matrix (Fin s × Fin b) (Fin c) ℂ)
    (hW : Wᴴ * W = 1 ∧ W * Wᴴ = 1) :
    (∫ U : Matrix.unitaryGroup (Fin c) ℂ,
      traceNorm (decouplingMarginal W phi U -
        Matrix.kronecker (QAlgorithms.Papers.Independent.Information100.P08.maximallyMixed b) (traceLeft phi)) ^ 2 ∂Schur.unitaryHaar c) ≤
      (c : ℝ) * (Matrix.rank (traceLeft phi) : ℝ) * frobNorm phi ^ 2 / (s : ℝ) ^ 2 := by sorry

end QAlgorithms.Papers.Independent.Gap48.P38

end
