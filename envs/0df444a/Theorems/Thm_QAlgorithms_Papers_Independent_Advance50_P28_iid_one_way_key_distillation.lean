-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P28_iid_one_way_key_distillation
-- name    : QAlgorithms.Papers.Independent.Advance50.P28.iid_one_way_key_distillation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:00:56.794997+00:00
-- url     : https://prove2.me/theorems/dda94721-db86-4bcf-9331-4f05e876cf95
-- title:
--   IID one-way key distillation (98)–(99)
-- statement:
--   Take $n\ge1$ iid copies of a normalized source $(A,B,E)$ with finite abelian $A$ and measurable side information. Write $\phi_B(t)$ and $\phi_E(t)$ for its conditional phi functions. For all positive integers $M,L$, there is a single one-way protocol with a uniform $M$-valued Alice key and public transcript $X+A^n$ such that
--   $$\epsilon_B\le3\inf_{0\le s\le1}(ML)^s|A|^{-ns}e^{n\phi_B(-s)},\qquad d_1\le9\inf_{0\le t\le1/2}\frac{|A|^{nt}e^{n\phi_E(t)}}{L^t}.$$
--   Bob and Eve observe the whole transcript together with their respective original side information. Both guarantees concern the same stochastic protocol and the actual iid source, without an unrelated input distribution. For side variable $V=B$ or $E$, $\phi_V(t)=\log\mathbb E_V[(\sum_aP(a|V)^{1/(1-t)})^{1-t}]$; zero-probability letters contribute zero.
-- source:
--   Tight exponential analysis of universally composable privacy amplification and its applications, arXiv:1010.1358v5, PDF p. 16, IID one-way key distillation (98)–(99)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P28

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology

namespace QAlgorithms.Papers.Independent.Advance50.P28

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Hayashi, PDF p.16, (98)–(99): ONE protocol meets both iid bounds; no unrelated
input law p is introduced. The decoder and Eve both receive the whole public mask. -/
theorem iid_one_way_key_distillation {A B E : Type*} [AddCommGroup A] [Fintype A]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [MeasurableSpace E]
    (muB : Measure B) (muE : Measure E) [IsProbabilityMeasure muB] [IsProbabilityMeasure muE]
    (pB : B → A → ℝ) (pE : E → A → ℝ)
    (hp : CompatibleMarginals muB pB muE pE)
    (n M L : ℕ) (hn : 0 < n) (hM : 0 < M) (hL : 0 < L) :
    ∃ C : WiretapCode (Fin n → A) ((Fin n → A) × (Fin n → B)) M,
      wiretapDecodingError (Measure.count.prod (Measure.pi (fun _ : Fin n => muB)))
        (generalAdditiveDensity (conditionalIid pB n)) C ≤
        3 * sInf ((fun s : ℝ => (M * L : ℝ≥0∞) ^ s * ENNReal.ofReal (Real.exp
          ((n : ℝ) * (-s * Real.log (Fintype.card A : ℝ) + conditionalPhi muB pB (-s))))) ''
            Set.Icc 0 1) ∧
      codeLeakage (Measure.count.prod (Measure.pi (fun _ : Fin n => muE)))
        (generalAdditiveDensity (conditionalIid pE n)) C ≤
        9 * sInf ((fun t : ℝ => ENNReal.ofReal (Real.exp
          ((n : ℝ) * (t * Real.log (Fintype.card A : ℝ) + conditionalPhi muE pE t))) /
            (L : ℝ≥0∞) ^ t) '' Set.Icc 0 (1 / 2)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P28

end
