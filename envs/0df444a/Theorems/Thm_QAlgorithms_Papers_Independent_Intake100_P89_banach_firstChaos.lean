-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P89_banach_firstChaos
-- name    : QAlgorithms.Papers.Independent.Intake100.P89.banach_firstChaos
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:35:34.793986+00:00
-- url     : https://prove2.me/theorems/ff34331a-d530-46e1-949e-e7b026696d93
-- title:
--   Lemma 2.3: Banach first-chaos representation
-- statement:
--   Let $G$ be the closed linear span of $\ell(W)$, $\ell\in B^*$, in $L^2(P)$ for a Borel centered Gaussian element $W$ in a real separable Banach space. All Pettis integrals $JH=E[HW]$ are defined for $H\in L^2(P)$. On $G$, $J$ is one-to-one, has range exactly the RKHS, and
--   $$\langle JH_1,JH_2\rangle_H=E[H_1H_2].$$
--   The norm identity is restricted to first chaos; the whole $L^2$ space is not identified isometrically with $H$.
-- source:
--   Reproducing kernel Hilbert spaces of Gaussian priors, arXiv:0805.3252v1, PDF p. 5, Lemma 2.3: Banach first-chaos representation

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P89

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory

open scoped Topology BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Intake100.P89

universe u v w

variable {Omega : Type u} [MeasurableSpace Omega]

section BanachResults

variable {B : Type v} [NormedAddCommGroup B] [NormedSpace ℝ B]

variable [hComplete : CompleteSpace B] [hSeparable : TopologicalSpace.SeparableSpace B]

variable (P : Measure Omega) [hP : IsProbabilityMeasure P]

include hP hComplete hSeparable

/-- Lemma 2.3: Banach first-chaos representation, arXiv:0805.3252v1, PDF p.5.
Printed H2 W in the pairing is read as E[H2 W], as fixed by the construction and proof. Pettis synthesis is implemented by the equal Bochner integral. -/
theorem banach_firstChaos
(W : Omega → B) (hW : BorelCenteredGaussianElement P W) :
    (∀ h : L2 P, Integrable (fun o => h o • W o) P ∧
      ∀ l : B →L[ℝ] ℝ, l (synthesis P W h) = ∫ o, h o * l (W o) ∂P) ∧
    Function.Injective (fun h : banachChaos P W => synthesis P W (h : L2 P)) ∧
    banachRKHS P W = Set.range (fun h : banachChaos P W => synthesis P W (h : L2 P)) ∧
    ∀ g h : banachChaos P W,
      banachInner P W (synthesis P W (g : L2 P)) (synthesis P W (h : L2 P)) = inner ℝ g h := by sorry

end BanachResults

end QAlgorithms.Papers.Independent.Intake100.P89

end
