-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P11_lemma_2_2
-- name    : QAlgorithms.Papers.Independent.Gap48.P11.lemma_2_2
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:30:08.513794+00:00
-- url     : https://prove2.me/theorems/d2240cab-0113-4d91-8b6f-b8a638fc509b
-- title:
--   Lemma 2.2: deterministic augmentation preserves approximate Markov form
-- statement:
--   Let $\rho_{XYE}$ be a normalized density operator, classical on finite nonempty registers $X,Y$, with a finite quantum register $E$. Let $f:X\times Y\to T$ be any function to a finite classical alphabet, and let $\varepsilon\ge0$. Write $\delta(\rho,\sigma)=\tfrac12\|\rho-\sigma\|_1$, and let $\rho_{X\leftrightarrow Y\leftrightarrow E}$ denote the reconstruction using the actual classical law and the actual conditional marginal $\rho_{E\mid Y=y}$ of the given state. Then
--
--   $$
--   \delta(\rho_{XYE},\rho_{X\leftrightarrow Y\leftrightarrow E})\le\varepsilon
--   \quad\Longrightarrow\quad
--   \delta(\rho_{Xf(X,Y)YE},\rho_{Xf(X,Y)\leftrightarrow Y\leftrightarrow E})\le\varepsilon.
--   $$
--
--   The added register contains the computed value $f(X,Y)$; all original registers and their quantum blocks are retained. The reconstruction on the right uses the augmented state's own marginals. The result permits deterministic classical information to be appended without increasing this error.
-- source:
--   Composing Quantum Protocols in a Classical Environment, arXiv:0804.1059v2, PDF p. 4, Lemma 2.2

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P11

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P11

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Lemma 2.2, PDF p.4; Appendix A.2, PDF p.19. The added register is computed
from both X and Y; the error remains eps. The comparison state is reconstructed
from the augmented state's own marginals, rather than an arbitrary Markov witness. -/
theorem lemma_2_2
    {X Y T E : Type*} [Fintype X] [Fintype Y] [Fintype T] [Fintype E]
    [Nonempty X] [Nonempty Y] [Nonempty E]
    (r : CQProbabilityBlocks (X × Y) E) (hr : IsNormalizedCQ r) (f : X → Y → T)
    (eps : ℝ) (heps : 0 ≤ eps)
    (hclose : cqDistance r (conditionalMarkovReconstruction r Prod.snd) ≤ eps) :
    cqDistance (appendClassicalFunction r f) (conditionalMarkovReconstruction (appendClassicalFunction r f) Prod.snd) ≤ eps := by sorry

end QAlgorithms.Papers.Independent.Gap48.P11

end
