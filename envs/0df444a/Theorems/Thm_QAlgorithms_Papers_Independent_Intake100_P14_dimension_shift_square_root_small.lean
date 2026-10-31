-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P14_dimension_shift_square_root_small
-- name    : QAlgorithms.Papers.Independent.Intake100.P14.dimension_shift_square_root_small
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:15:36.410962+00:00
-- url     : https://prove2.me/theorems/93a96698-5dc2-47bf-afe2-5334005949a7
-- title:
--   Lemma 34: square-root smallness of dimension shifting
-- statement:
--   Let $G$ be a Hausdorff locally compact second countable group, let $A$ be a Polish Abelian topological group with a jointly continuous action $T$ by automorphisms, and let $p\ge1$. Cochains are Borel maps on $G^p$, cocycle and coboundary equations hold Haar almost everywhere, and $d$ is the unnormalized inhomogeneous bar differential. In degree zero, $C^0=A$ and $B^0=0$. Suppose $G$ is compact, $\mu$ is probability Haar measure, and the compatible translation-invariant metric $\rho$ on $A$ is action invariant. A map $f$ is $\varepsilon$-small when $\varepsilon>0$ and $\mu\{\rho(0,f)>\varepsilon\}<\varepsilon$. For a cocycle $\psi$ and $0<\varepsilon<1$ with this smallness, define
--
--   $$Q\psi(g_1,\ldots,g_{p-1})(h)=(-1)^p\psi(g_1,\ldots,g_{p-1},(g_1\cdots g_{p-1})^{-1}h).$$
--
--   Then $Q\psi$ is $\sqrt\varepsilon$-small for the probability metric $\rho_0(f,h)=\inf\{r>0:f-h\text{ is }r\text{-small}\}$. In particular, with $\mu_{p-1}$ the product Haar measure,
--
--   $$\mu_{p-1}\left\{g:\mu\{h:\rho(0,Q\psi(g)(h))\ge\sqrt\varepsilon\}\ge\sqrt\varepsilon\right\}<\sqrt\varepsilon.$$
--
--   This controls dimension shifting in the convergence-in-probability metric.
-- source:
--   Continuity properties of measurable group cohomology, arXiv:1004.4937v4, PDF p. 16, Lemma 34: square-root smallness of Q

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P14

noncomputable section

open MeasureTheory Filter Set

open scoped BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Intake100.P14

universe u v w

section LocallyCompact

variable {G : Type u} [Group G] [TopologicalSpace G]
    [hTG : IsTopologicalGroup G] [hT2 : T2Space G]
    [hLC : LocallyCompactSpace G] [hSC : SecondCountableTopology G]
    [MeasurableSpace G] [hBG : BorelSpace G]
    {A : Type v} [AddCommGroup A] [MetricSpace A] [hTA : IsTopologicalAddGroup A]
    [hPA : PolishSpace A] [MeasurableSpace A] [hBA : BorelSpace A]
    (mu : Measure G) [hHaar : mu.IsHaarMeasure] (T : ModuleAction G A)

include hTG hT2 hLC hSC hBG hTA hPA hBA hHaar

/-- Lemma 34, PDF p.16: square-root smallness for Q, including the nested-measure
estimate, with all three square roots and both non-strict inner comparisons. -/
theorem dimension_shift_square_root_small [CompactSpace G] [IsProbabilityMeasure mu]
    (hiso : ActionIsometric T) (p : ℕ) (epsilon : ℝ)
    (hepsilon : 0 < epsilon) (hepsilon_one : epsilon < 1)
    (f : GroupPower G (p + 1) → A) (hf : IsCocycle mu T.act (p + 1) f)
    (hsmall : Small (powerMeasure mu (p + 1)) f epsilon) :
    Small (powerMeasure mu p)
      (fun g => probabilityDistance mu (fun _ => 0) (dimensionShiftQ p f g))
      (Real.sqrt epsilon) ∧
    powerMeasure mu p {g | ENNReal.ofReal (Real.sqrt epsilon) ≤
      mu {h | Real.sqrt epsilon ≤ dist 0 (dimensionShiftQ p f g h)}} <
      ENNReal.ofReal (Real.sqrt epsilon) := by sorry

end LocallyCompact

end QAlgorithms.Papers.Independent.Intake100.P14

end
