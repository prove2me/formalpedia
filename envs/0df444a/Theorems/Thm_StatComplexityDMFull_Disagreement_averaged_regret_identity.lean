-- Prove2me | Theorems.Thm_StatComplexityDMFull_Disagreement_averaged_regret_identity
-- name    : StatComplexityDMFull.Disagreement.averaged_regret_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:54:55.615968+00:00
-- url     : https://prove2.me/theorems/b3e8a1d8-1068-426b-9baf-5fa17e47d5f5
-- title:
--   §E.2.2 — the fully averaged regret identity
-- statement:
--   Let $\mu$ be a Radon prior over the discrete model class with mean rewards $f^M:\Pi\to[0,1]$ and selected optimizers $\pi_M$. Let $p\in\Delta(\Pi)$ be any Radon decision law. All model and decision draws below are independent. Then
--
--   $$\mathbb E_{M\sim\mu}\mathbb E_{\pi\sim p}[f^M(\pi_M)-f^M(\pi)]
--   =\mathbb E_{\widetilde M\sim\mu}\mathbb E_{M\sim\mu}\mathbb E_{\pi\sim p}
--   [f^M(\pi_M)-f^{\widetilde M}(\pi)].$$
--
--   This is the fully averaged identity directly after “Hence, it suffices bound the quantity” in the proof. The decision law is arbitrary, and in particular may later be the posterior-sampling law. Every tilded variable is bound by its own expectation; this item does not transcribe the later display with inconsistent free and bound variables.
--
--   Differences from the source:
--   - generalization: reward-observation probability kernels with bounded means and selected maximizers → arbitrary measurable mean data in [0,1] with selected maximizers; reason: each source kernel supplies its bounded measurable expectation and selected optimizer; no other kernel data enter these formulas
--   - encoding: Radon probability laws with the Borel convention and discrete model topology → RadonLaw packages a probability measure and compact inner regularity; source model indices have the discrete topology; reason: these are the source probability class and default model topology, with no support bound or decision-space discreteness
-- source:
--   Foster, Kakade, Qian and Rakhlin, The Statistical Complexity of Interactive Decision Making, arXiv:2112.13487v3, p. 106, Section E.2.2, fully averaged regret identity in the proof of Theorem 6.2 (unnumbered)

import Mathlib
import Definitions.Def_StatComplexityDMFull_Disagreement_RadonLaw
import Definitions.Def_StatComplexityDMFull_Disagreement_MeanModel

set_option autoImplicit false

namespace StatComplexityDMFull.Disagreement

/-- Section E.2.2, fully averaged identity, p. 106. The arbitrary decision law is independent. -/
theorem averaged_regret_identity {M A : Type*} [TopologicalSpace M] [DiscreteTopology M]
    [MeasurableSpace M] [BorelSpace M] [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]
    (μ : RadonLaw M) (D : MeanModel M A) (p : RadonLaw A) :
    (∫ m, (∫ a, D.mean m (D.optimal m) - D.mean m a ∂p.val) ∂μ.val) =
      ∫ n, (∫ m, (∫ a, D.mean m (D.optimal m) - D.mean n a ∂p.val) ∂μ.val) ∂μ.val := by sorry

end StatComplexityDMFull.Disagreement
