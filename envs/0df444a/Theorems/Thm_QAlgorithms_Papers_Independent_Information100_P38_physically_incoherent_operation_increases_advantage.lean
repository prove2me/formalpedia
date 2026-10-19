-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P38_physically_incoherent_operation_increases_advantage
-- name    : QAlgorithms.Papers.Independent.Information100.P38.physically_incoherent_operation_increases_advantage
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:12:41.113734+00:00
-- url     : https://prove2.me/theorems/65ac8829-edec-4ffa-a762-2b64429b8dea
-- title:
--   Appendix C / Section III p.10
-- statement:
--   Let $H=\operatorname{diag}(0,1,2)$ and let $M=\{A,I-A\}$, where $A=\left(\begin{smallmatrix}11/50&-7/20&0\\-7/20&29/50&0\\0&0&29/50\end{smallmatrix}\right)$. Define $\Lambda(\rho)=K_1\rho K_1^\dagger+K_2\rho K_2^\dagger$ with $K_1=\operatorname{diag}(1,1,0)$ and $K_2=|0\rangle\langle2|$. This Kraus family is trace preserving and admits a PIO implementation by orthogonal diagonal projectors and incoherent unitaries. Both $M$ and $M'=\Lambda^\dagger(M)$ are POVMs; the first effect of $M'$ replaces $A_{22}$ by $11/50$. Their exact global maxima are
--
--   $$A_H^M=\frac{35\sqrt{1549}}{5589}<\frac{35\sqrt{1549}}{5049}=A_H^{M'}.$$
--
--   Both maxima are attained at $\rho_*=\left(\begin{smallmatrix}1/3&-1/3&0\\-1/3&1/3&0\\0&0&1/3\end{smallmatrix}\right)$, which is a density matrix. This is failure of monotonicity under the displayed physically incoherent operation; the state channel is not required to be unital.
-- source:
--   All coherent measurements provide observational ergotropic advantage, arXiv:2609.18735v1, PDF p. 13, Appendix C / Section III p.10

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P38

open scoped ComplexConjugate Matrix

/-- Paper p.10 and Appendix C pp.13–15, Eqs.(C2),(C55),(C58): the displayed PIO
strictly increases the advantage. The exact GLOBAL maxima and their common maximizing
state are conclusions, not assumptions; no bistochasticity is imposed. -/
theorem physically_incoherent_operation_increases_advantage :
    let M := advantagePIOOriginal
    let Mnew := fun u => ergotropicKrausDual advantagePIOKraus (M u)
    let E : Fin 3 → ℝ := ![0, 1, 2]
    ergotropicPIOFamily advantagePIOKraus ∧
    (∑ j, (advantagePIOKraus j)ᴴ * advantagePIOKraus j) = 1 ∧
    IsPOVM M ∧ IsPOVM Mnew ∧
    Mnew = ergotropicBinary !![11/50, -7/20, 0; -7/20, 29/50, 0; 0, 0, 11/50] ∧
    IsDensityMatrix advantagePIOInput ∧
    observationalAdvantage E M = 35 * Real.sqrt 1549 / 5589 ∧
    observationalAdvantage E Mnew = 35 * Real.sqrt 1549 / 5049 ∧
    observationalErgotropy E M advantagePIOInput - incoherentErgotropy E advantagePIOInput =
      observationalAdvantage E M ∧
    observationalErgotropy E Mnew advantagePIOInput - incoherentErgotropy E advantagePIOInput =
      observationalAdvantage E Mnew ∧
    observationalAdvantage E M < observationalAdvantage E Mnew := by sorry

end QAlgorithms.Papers.Independent.Information100.P38

end
