-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P73_information_spectrum_complement
-- name    : QAlgorithms.Papers.Independent.Intake100.P73.information_spectrum_complement
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:54:07.531848+00:00
-- url     : https://prove2.me/theorems/52fb1ca5-4d72-4a4a-a2ec-4c7e636fec78
-- title:
--   Complementary-event formulas for both spectral families
-- statement:
--   Let $\mathbf W=(W^n)$ be any sequence of classical discrete stochastic channels and $\mathbf p=(p_n)$ any sequence of normalized input laws. All logarithms are natural. For an input-law sequence $\mathbf p=(p_n)$ and channel sequence $\mathbf W$, put $T_n(a)=\mathbb P_{p_n(x)W_x^n(y)}\{n^{-1}\log[W_x^n(y)/W_{p_n}^n(y)]>a\}$. Define $\underline I(\epsilon\mid\mathbf p,\mathbf W)=\inf\{a:\liminf_nT_n(a)\le\epsilon\}$ and $\overline I(\epsilon\mid\mathbf p,\mathbf W)=\inf\{a:\limsup_nT_n(a)\le\epsilon\}$. At $\epsilon=1$ use the strict tail bound $<1$. Spectra and numerical extrema are extended-valued.
--
--   Write $L_n(a)=\mathbb P\{n^{-1}\log[W_x^n(y)/W_{p_n}^n(y)]\le a\}$. For $0\le\epsilon<1$,
--   $$
--   \underline I(\epsilon)=\sup\{a:\limsup_nL_n(a)<1-\epsilon\},\qquad
--   \overline I(\epsilon)=\sup\{a:\liminf_nL_n(a)<1-\epsilon\}.
--   $$
--   At $\epsilon=1$, replace the two low-event comparisons by $\le0$. This separate endpoint clause corrects the unqualified displayed strict comparison in the source. These identities connect upper-tail and complementary low-event descriptions with opposite limit operations.
-- source:
--   General non-asymptotic and asymptotic formulas in channel resolvability and identification capacity and their application to wire-tap channel, arXiv:cs/0503088v2, PDF p. 7, Unnumbered information-spectrum complementary-event formulas

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P73

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P73

open Filter

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable Classical.decEq

universe u

/-- Hayashi, PDF p.7: BOTH complementary spectral expressions. At epsilon=1
use low<=0, correcting the impossible strict low<0 in the unqualified display. -/
theorem information_spectrum_complement {X Y : ℕ → Type*}
    (W : (k : ℕ) → X k → Y k → ℝ≥0∞) (hW : ∀ k, IsDiscreteStochastic (W k))
    (p : (k : ℕ) → PMF (X k)) (eps : ℝ) (heps : 0 ≤ eps) (heps1 : eps ≤ 1) :
    epsilonInformationSpectrum false W p eps = complementarySpectrum false W p eps ∧
    epsilonInformationSpectrum true W p eps = complementarySpectrum true W p eps := by sorry

end QAlgorithms.Papers.Independent.Intake100.P73

end
