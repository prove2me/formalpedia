-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P27_idealKD_perfect
-- name    : QAlgorithms.Papers.Independent.Support50.P27.idealKD_perfect
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T21:09:12.460331+00:00
-- url     : https://prove2.me/theorems/5ddb9a45-2c78-4ca8-97eb-4165582d1e3f
-- title:
--   §4.2: ideal KD has perfect equality, uniformity and privacy
-- statement:
--   Let $M$ be a public random key length with finite support, chosen with any distribution by the adversarial interface. Conditional on $M=m$, let $\widetilde\rho_m$ be Eve's normalized residual state. Ideal key distribution samples a fresh uniform $m$-bit string $K$, gives the same string to Alice and Bob, and leaves Eve's state equal to $\widetilde\rho_m$, independently of $K$. The value $m=0$ denotes abort and gives the unique empty key. If $p_{\mathrm{ideal}}^{(m)}(a,b)=2^{-m}\mathbf1_{a=b}$, then the equality-and-uniformity defect and conditional accessible information both vanish:
--
--   $$
--   \sum_m\Pr(M=m)\,\lVert p_{\mathrm{ideal}}^{(m)}-p_{\mathrm{ideal}}^{(m)}\rVert_1=0,
--   \qquad
--   \sum_m\Pr(M=m)\,I_{\mathrm{acc}}(K_AK_B:E\mid M=m)=0.
--   $$
--
--   Because $K_A=K_B=K$, the second expression is exactly the privacy requirement for $K$ in Eq. (5), optimized over measurements. Independence is conditional on the announced length, which Eve may know or control. This gives the perfect reference resource against which QKD output is compared.
-- source:
--   The Universal Composable Security of Quantum Key Distribution, arXiv:quant-ph/0409078v1, PDF p. 10, §4.2: ideal KD has perfect equality, uniformity and privacy

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P27

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P27

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Dependency50.P07
  (CQData ensembleMean ensembleInformation accessibleInformation)

open QAlgorithms.Papers.Independent.Dependency50.P24 (Key)

open QAlgorithms.Papers.Independent.Dependency50.P47 (cqMatrix)

attribute [local instance] Classical.decEq Classical.propDecidable

/-- PDF p.10, Section 4.2: ideal KD has zero equality/uniformity defect and
zero accessible information about its identical keys, conditional on length.
The pair of keys determines the same random variable as K in Eq.(5).
Devil may choose the length law and cause abort; unconditional independence
of Eve and the publicly announced length is not asserted. -/
theorem idealKD_perfect {L : ℕ} {E : Type} [Fintype E] [Nonempty E]
    (D : KeyData L E) :
    equalityUniformityDefect D.lengthProb (idealBranch D) = 0 ∧
      (∑ m, D.lengthProb m * accessibleInformation (idealBranch D m)) = 0 := by sorry

end QAlgorithms.Papers.Independent.Support50.P27

end
