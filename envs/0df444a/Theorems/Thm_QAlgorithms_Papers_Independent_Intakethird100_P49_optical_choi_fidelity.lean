-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P49_optical_choi_fidelity
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P49.optical_choi_fidelity
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:42:48.229923+00:00
-- url     : https://prove2.me/theorems/cc2f8964-b836-49c5-a7b1-4fdcc25e373c
-- title:
--   Supplement II, Eqs.(125)–(129): optical Choi fidelity
-- statement:
--   Let $0\le\eta\le1$ and let the actual real image-mode overlap satisfy $-1\le\delta\le1$. Set $\eta_\pm=(1\pm\delta)\eta/2$. The coherent vacuum/one-photon channels $\mathcal E_\pm:2\to3$ send $|0\rangle$ to output vacuum and the surviving $|1\rangle$ to $\sqrt{\eta_+}|+\rangle\pm\sqrt{\eta_-}|-\rangle$, with vacuum loss probability $1-\eta$. Their anti-Bell Choi states, in reference-first order, are
--
--   $$\rho_\pm=\frac{1+\eta}{2}|\Psi_\pm\rangle\langle\Psi_\pm|+\frac{1-\eta}{2}|0,0\rangle\langle0,0|,$$
--
--   where $|\Psi_\pm\rangle=(|1,0\rangle+\sqrt{\eta_+}|0,+\rangle\pm\sqrt{\eta_-}|0,-\rangle)/\sqrt{1+\eta}$. Both channels are CPTP and
--
--   $$F(\rho_+,\rho_-)=\frac{1-\eta+|1+\delta\eta|}{2}=1-\frac{\eta(1-\delta)}2.$$
--
--   The same fidelity holds for canonical normalized Choi states, since a common reference $X$ changes Bell to anti-Bell. This gives an exact optical overlap, including full loss and vanishing mode separation.
-- source:
--   Fundamental limits to quantum channel discrimination, arXiv:1803.02834v4, PDF p. 15, Supplement II, Eqs.(125)–(129): optical Choi fidelity

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P49

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P49

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P63 (Mat tensorPower)

open QAlgorithms.Papers.Independent.Dependency50.P18 (bipartiteTensor)

open QAlgorithms.Papers.Independent.Information100.P71 (diamond AdaptiveTest adaptiveInput adaptiveAccept)

open QAlgorithms.Papers.Independent.Bridge50.P25
  (LOCCOn normalizedChannelChoi TwoWayGenerationCode TwoWayChannelProtocol
   generationCodeError twoWayGenerationCapacity sendChannelRegister StateFunctional
   IsDimensionChangingLOCCMonotone privateStateInPartyOrder)

open QAlgorithms.Papers.Independent.Support50.P07 (amplitudeDampingChannel)

/-- Supplement II, PDF p.15, (125)--(129): coherent optical Choi states
and their exact root fidelity. Printed (121)'s fixed minus is corrected using
(117),(118),(124). Anti-Bell differs from canonical Bell by a common reference X,
which preserves fidelity. Joint-vacuum leakage and both parameter endpoints remain. -/
theorem optical_choi_fidelity (eta delta : ℝ)
    (heta : eta ∈ Set.Icc 0 1) (hdelta : delta ∈ Set.Icc (-1) 1) :
    (∀ sign : Bool, IsChannel (opticalChannel eta delta sign) ∧
      opticalChoi eta delta sign =
        (((1+eta)/2 : ℝ) : ℂ) • pureDensity (opticalPsi eta delta sign) +
        (((1-eta)/2 : ℝ) : ℂ) • Matrix.single (0,0) (0,0) 1) ∧
    rootFidelity (opticalChoi eta delta false) (opticalChoi eta delta true) =
      (1-eta+|1+delta*eta|)/2 ∧
    rootFidelity (opticalChoi eta delta false) (opticalChoi eta delta true) =
      1-eta*(1-delta)/2 ∧
    rootFidelity (normalizedChannelChoi (opticalChannel eta delta false))
      (normalizedChannelChoi (opticalChannel eta delta true)) = 1-eta*(1-delta)/2 := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P49

end
