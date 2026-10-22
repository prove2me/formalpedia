-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P38_entropyPotentials
-- name    : QAlgorithms.Papers.Independent.Gap48.P38.entropyPotentials
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:11:16.105561+00:00
-- url     : https://prove2.me/theorems/79c29a24-bc96-4a35-b6cd-ddad61c3a17f
-- title:
--   §V, unnumbered: entropy potentials and optimal costs (corrected dynamic sign)
-- statement:
--   Let $|\psi\rangle^{ABCD}$ be a unit vector on nonempty finite complex registers, and use bit entropies of its actual marginals. Define dynamic potentials $K_i=I(AC;D)/2$, $K_f=I(A;D)/2$ and static potentials $S_i=I(AC;B)/2$, $S_f=I(A;BC)/2$. For the numerical corner costs $Q^*=I(C;D\mid B)/2$ and $E^*=[I(A;C)-I(B;C)]/2$ from equation (2),
--
--   $$K_i-K_f=\tfrac12I(C;D\mid A)=Q^*,\qquad S_f-S_i=E^*.$$
--
--   These identities express the source's entropy-potential interpretation of the optimal corner expressions.
--
--   **Formalization Note** Page 11 prints $K_f-K_i$ for the dynamic difference. The statement corrects this to $K_i-K_f$, as forced by its own definitions and the entropy chain rule. For a Bell pair on $CD$ with $A,B$ trivial, $K_i=1$, $K_f=0$, and $Q^*=1$. Independent moderation of this source correction is required.
-- source:
--   Optimal quantum source coding with quantum information at the encoder and decoder, arXiv:0706.2907v2, PDF p. 11, §V, unnumbered: entropy potentials and optimal costs (corrected dynamic sign)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P38

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Gap48.P38

/-- Section V, PDF p.11: entropy potentials and the corner costs (2).
SOURCE CORRECTION: the printed K_final-K_initial has the opposite sign to
its own definitions; changed to K_initial-K_final, forced by the CMI chain
rule and the Bell(C,D) example. Static potential uses S_final-S_initial as printed.
Independent moderation of this correction is still required. -/
theorem entropyPotentials
    (I : Fin 4 → Type) [∀ i, Fintype (I i)] [∀ i, Nonempty (I i)]
    (psi : EuclideanSpace ℂ (∀ i, I i)) (hpsi : ‖psi‖ = 1) :
    let rho := pureDensity psi
    let Kinitial := registerMutualInfo I rho {0,2} {3} / 2
    let Kfinal := registerMutualInfo I rho {0} {3} / 2
    let Sinitial := registerMutualInfo I rho {0,2} {1} / 2
    let Sfinal := registerMutualInfo I rho {0} {1,2} / 2
    Kinitial - Kfinal = registerCMI I rho {2} {3} {0} / 2 ∧
    Kinitial - Kfinal = cornerQ I rho ∧ Sfinal - Sinitial = cornerE I rho := by sorry

end QAlgorithms.Papers.Independent.Gap48.P38

end
