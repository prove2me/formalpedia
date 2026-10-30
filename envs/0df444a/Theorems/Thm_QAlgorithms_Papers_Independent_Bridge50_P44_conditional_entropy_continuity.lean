-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P44_conditional_entropy_continuity
-- name    : QAlgorithms.Papers.Independent.Bridge50.P44.conditional_entropy_continuity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:16:02.978036+00:00
-- url     : https://prove2.me/theorems/cf5d211f-61df-4ceb-b747-ef4ab4a59a83
-- title:
--   Theorem A.9 (From [AF04]): conditional-entropy continuity
-- statement:
--   Let $\rho_{AB},\sigma_{AB}$ be density matrices on finite-dimensional nonzero systems with $\dim A=d_A$, and put $\varepsilon=D(\rho,\sigma)\le1/4$. With $S(A|B)=S(AB)-S(B)$ in natural logarithms and $h(t)=-t\log t-(1-t)\log(1-t)$, using $0\log0=0$,
--
--   $$|S(A|B)_\rho-S(A|B)_\sigma|\le8\varepsilon\log d_A+2h(2\varepsilon).$$
--
--   This is the stated conditional-entropy continuity bound attributed to Alicki and Fannes [AF04]. The finite-matrix domain makes the entropy difference well defined. The source does not print a log base; natural logs are used consistently with its subsequent Pinsker coefficient.
-- source:
--   Cryptographic security of quantum key distribution, arXiv:1409.3525v1, PDF p. 43, Theorem A.9 (From [AF04]): conditional-entropy continuity

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P44

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Bridge50.P44

open QAlgorithms

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize)

open QAlgorithms.Papers.Independent.Dependency50.P24 (cqState)

open QAlgorithms.Papers.Independent.Frontier18.P08 (partialTraceFirst)

open QAlgorithms.Papers.Independent.Information100.P76 (maximallyMixed)

open QAlgorithms.Papers.Independent.Frontier18.P08 (conditionalEntropyNats)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF p.43, Theorem A.9, attributed to Alicki--Fannes [AF04]. Natural logs
are chosen consistently with the exact Pinsker coefficient on p.44. This is
the finite-matrix entropy-difference domain, with epsilon the actual distance. -/
theorem conditional_entropy_continuity {d e : ℕ} (hd : 0 < d) (he : 0 < e)
    (rho sigma : Matrix (Fin d × Fin e) (Fin d × Fin e) ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (epsilon : ℝ) (hdistance : traceDistance rho sigma = epsilon) (hsmall : epsilon ≤ 1 / 4) :
    |conditionalEntropyNats rho - conditionalEntropyNats sigma| ≤
      8 * epsilon * Real.log d + 2 * Real.binEntropy (2 * epsilon) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P44

end
