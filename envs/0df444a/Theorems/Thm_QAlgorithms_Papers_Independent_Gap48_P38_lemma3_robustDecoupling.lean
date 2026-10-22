-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P38_lemma3_robustDecoupling
-- name    : QAlgorithms.Papers.Independent.Gap48.P38.lemma3_robustDecoupling
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:05:44.908573+00:00
-- url     : https://prove2.me/theorems/d71970af-3436-4e31-9913-ca0a36ee33a7
-- title:
--   Lemma 3 (Robust one-shot decoupling)
-- statement:
--   Let $C,E,S,\widehat B$ be nonempty finite complex registers. Let $\psi^{CE},\varphi^{CE}$ be density matrices, let $\epsilon>0$, and suppose $\|\psi-\varphi\|_1\le\epsilon$, using the full trace norm. Fix a unitary identification $W:C\to S\widehat B$, and put $\psi_U=(WU\otimes I_E)\psi(WU\otimes I_E)^\dagger$. Let $\overline\psi=\int\psi_U\,dU$, where $dU$ is normalized Haar probability on $U(C)$. With $\pi^{\widehat B}=I_{\widehat B}/|\widehat B|$ and actual partial traces,
--
--   $$\|\overline\psi^{\widehat BE}-\pi^{\widehat B}\otimes\psi^E\|_1\le2\epsilon+\sqrt{\frac{|C|\,\operatorname{rank}(\varphi^E)\,\|\varphi^{CE}\|_2^2}{|S|^2}}.$$
--
--   This is exactly the printed norm-of-average estimate. It does not assert the stronger average-of-norms bound used informally later in the paper. Finite-dimensional continuous integrands on the compact unitary group ensure integrability.
-- source:
--   Optimal quantum source coding with quantum information at the encoder and decoder, arXiv:0706.2907v2, PDF p. 6, Lemma 3 (Robust one-shot decoupling)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P38

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Gap48.P38

/-- Lemma 3 (robust one-shot decoupling), PDF p.6, eq.(16), appendix pp.11--12.
The norm is OUTSIDE the Haar average, as printed, not the average of norms.
The matrix integral uses the finite elementwise norm; all integrands are
continuous on compact U(c), hence Bochner integrable;
no unproved integrability assumption is added to the source's hypotheses. -/
theorem lemma3_robustDecoupling
    (c s b e : ℕ) (hc : 0 < c) (hs : 0 < s) (hb : 0 < b) (he : 0 < e)
    (psi phi : Matrix (Fin c × Fin e) (Fin c × Fin e) ℂ)
    (hpsi : IsDensityMatrix psi) (hphi : IsDensityMatrix phi)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (hclose : traceNorm (psi - phi) ≤ epsilon)
    (W : Matrix (Fin s × Fin b) (Fin c) ℂ)
    (hW : Wᴴ * W = 1 ∧ W * Wᴴ = 1) :
    traceNorm ((∫ U : Matrix.unitaryGroup (Fin c) ℂ,
      decouplingMarginal W psi U ∂Schur.unitaryHaar c) -
      Matrix.kronecker (QAlgorithms.Papers.Independent.Information100.P08.maximallyMixed b) (traceLeft psi)) ≤
      2 * epsilon + Real.sqrt ((c : ℝ) * (Matrix.rank (traceLeft phi) : ℝ) *
        frobNorm phi ^ 2 / (s : ℝ) ^ 2) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P38

end
