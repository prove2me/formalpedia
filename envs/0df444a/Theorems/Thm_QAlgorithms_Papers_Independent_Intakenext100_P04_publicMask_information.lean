-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P04_publicMask_information
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P04.publicMask_information
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T03:51:16.745868+00:00
-- url     : https://prove2.me/theorems/6ab058f6-6161-4da0-bfd5-8163f6c05ab5
-- title:
--   A public additive mask combines the two information imperfections
-- statement:
--   Let $Y\in\mathbb F_2^r$ be obtained by the X measurement of a qubit factor of an arbitrary positive trace-class joint state, and let $p$ be its distribution. Choose a fresh independent uniform $W\in\mathbb F_2^r$, announce $W$, and set $K=W+Y$. Include $W$ with all Eve's existing data, and allow her measurement to depend on $W$. For every $r\ge0$, $K$ is marginally uniform and
--
--   $$
--   I_{\rm acc}(K:W,E)=r-H(p)+I_{\rm acc}(Y:E).
--   $$
--
--   Moreover, there is an absolute $r_0$ such that, for $r\ge\max\{r_0,1\}$, $0\le\eta\le1/2$, and $\langle0|\rho_Q|0\rangle_Z\ge1-\eta$,
--
--   $$
--   I_{\rm acc}(K:W,E)<3r\eta+h(\eta)\quad(\eta>0),\qquad I_{\rm acc}(K:W,E)=0\quad(\eta=0).
--   $$
--
--   This combines nonuniformity and Eve's accessible information into the paper's single parameter. The mask is public and consumes no additional secret bits; the identity is not an identity for quantum mutual information.
-- source:
--   Secure quantum key distribution with an uncharacterized source, arXiv:quant-ph/0208155v2, PDF p. 4, Eq.(13)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P04

noncomputable section

universe u v w

namespace QAlgorithms.Papers.Independent.Intakenext100.P04

open QAlgorithms

open QAlgorithms.Papers.Independent.Dependency50.P13
  (State IsTraceClass IsPositive operatorTrace)

open QAlgorithms.Papers.Independent.Advance50.P18 (keyEntropy)

open scoped ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Koashi–Preskill PDF p.4, Eq.(13): the public additive mask combines the
two imperfections in accessible information. Uniformity of K is marginal;
W remains inside Eve's data, and her POVM may depend on W. -/
theorem publicMask_information :
    (∀ (r : ℕ) {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] {I : Type v} (b : HilbertBasis I ℂ H)
      (rho : State b) (A : QubitFactor r H),
      (∀ k, maskedKeyLaw (keyLaw b rho A) k = ((2 : ℝ) ^ r)⁻¹) ∧
      maskedAccessibleInfo b rho A =
        (r : ℝ) - keyEntropy (keyLaw b rho A) + accessibleKeyInfo b rho A) ∧
    (∃ r0 : ℕ, ∀ r : ℕ, r0 ≤ r → 1 ≤ r → ∀ eta : ℝ,
      0 ≤ eta → eta ≤ 1 / 2 →
      ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        {I : Type v} (b : HilbertBasis I ℂ H) (rho : State b) (A : QubitFactor r H),
      1 - eta ≤ (qubitMarginal b rho A 0 0).re →
      (0 < eta → maskedAccessibleInfo b rho A < 3 * r * eta + binEntropy2 eta) ∧
      (eta = 0 → maskedAccessibleInfo b rho A = 0)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P04

end
