-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P11_lemma_2_1
-- name    : QAlgorithms.Papers.Independent.Gap48.P11.lemma_2_1
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:29:20.44304+00:00
-- url     : https://prove2.me/theorems/1200c827-0850-46bb-9958-47a396727cda
-- title:
--   Lemma 2.1: three approximate conditional-independence bounds
-- statement:
--   Let $X,Y,Z$ be classical registers with finite nonempty alphabets, and let $E$ be a finite quantum register. All states below are normalized positive density operators, diagonal in their named classical registers. Write $\delta(\rho,\sigma)=\tfrac12\|\rho-\sigma\|_1$, and let $\varepsilon\ge0$. Each displayed reconstruction is calculated from the marginals of the given state: $\rho_{X\leftrightarrow Y\leftrightarrow E}=\sum_{x,y}P_{XY}(x,y)|xy\rangle\langle xy|\otimes\rho_{E\mid Y=y}$.
--
--   The following three implications hold:
--
--   $$
--   \begin{aligned}
--   \delta(\rho_{XYZE},\rho_{X\leftrightarrow Y\leftrightarrow ZE})\le\varepsilon
--   &\implies\delta(\rho_{XYZE},\rho_{X\leftrightarrow YZ\leftrightarrow E})\le2\varepsilon,\\
--   \delta(\rho_{XZE},\rho_X\otimes\rho_{ZE})\le\varepsilon
--   &\implies\delta(\rho_{XZE},\rho_{X\leftrightarrow Z\leftrightarrow E})\le2\varepsilon,\\
--   \delta(\rho_{XZE},I_X/|X|\otimes\rho_{ZE})\le\varepsilon
--   &\implies\delta(\rho_{XZE},\rho_{X\leftrightarrow Z\leftrightarrow E})\le4\varepsilon.
--   \end{aligned}
--   $$
--
--   Here $I_X$ is the identity on the classical $X$ register and $|X|$ is its alphabet size. In the first line, the right register of the first reconstruction contains both $Z$ and $E$. Zero-weight conditional fibers contribute zero. These bounds permit changing the conditioning register while controlling the error in conditional independence.
-- source:
--   Composing Quantum Protocols in a Classical Environment, arXiv:0804.1059v2, PDF p. 4, Lemma 2.1

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P11

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P11

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Lemma 2.1, PDF p.4; Appendix A.1, PDF p.19. All three clauses use the
marginals of the same given normalized state. The constants are 2, 2, and 4;
nonnegative error bounds are not capped at 1. The first right register includes Z. -/
theorem lemma_2_1
    {X Y Z E : Type*} [Fintype X] [Fintype Y] [Fintype Z] [Fintype E]
    [Nonempty X] [Nonempty Y] [Nonempty Z] [Nonempty E]
    (eps : ℝ) (heps : 0 ≤ eps) :
    (∀ r : CQProbabilityBlocks (X × Y × Z) E, IsNormalizedCQ r →
      cqDistance r (reconstructRight r) ≤ eps →
      cqDistance r (conditionalMarkovReconstruction r (fun c => c.2)) ≤ 2 * eps) ∧
    (∀ r : CQProbabilityBlocks (X × Z) E, IsNormalizedCQ r →
      cqDistance r (productMarginals r) ≤ eps →
      cqDistance r (conditionalMarkovReconstruction r Prod.snd) ≤ 2 * eps) ∧
    (∀ r : CQProbabilityBlocks (X × Z) E, IsNormalizedCQ r →
      cqDistance r (uniformProduct r) ≤ eps →
      cqDistance r (conditionalMarkovReconstruction r Prod.snd) ≤ 4 * eps) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P11

end
