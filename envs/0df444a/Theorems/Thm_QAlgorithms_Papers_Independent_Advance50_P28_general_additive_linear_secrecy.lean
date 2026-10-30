-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P28_general_additive_linear_secrecy
-- name    : QAlgorithms.Papers.Independent.Advance50.P28.general_additive_linear_secrecy
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:59:30.202412+00:00
-- url     : https://prove2.me/theorems/0d087d07-5255-42f7-8114-f3e35a2f1626
-- title:
--   General additive linear coding secrecy (92)–(94)
-- statement:
--   Let $A$ be finite and nonempty, let $\mu$ be a probability measure on a measurable space $E$, and let $p_e(a)$ be a measurable conditional probability vector. Define $\phi(t)=\log\int(\sum_a p_e(a)^{1/(1-t)})^{1-t}\,d\mu(e)$ and $g_E(s)=-\log\int\sum_a p_e(a)^{1+s}\,d\mu(e)$, with $g_E(0)=0$. Leakage is full $L^1$ distance from a uniform key independent of Eve. Let $A=G$ be a finite abelian group and use $n\ge1$ iid copies of the joint additive noise $(G,E)$. Let a fixed block subgroup and public random size-$L$ subgroups obey Condition 4, with $L=e^{nR}$. Then
--   $$\mathbb E_Xd_1\le3\frac{\exp(n[t\log|G|+\phi(t)])}{L^t}\quad(0<t<1/2),\qquad\mathbb E_Xd_1\le3e^{-n e_\phi(\log|G|-R)}.$$
--   Here $e_\phi(u)=\max_{0\le t\le1/2}[-\phi(t)-tu]$. These are the one-shot bounds at $n=1$ and the iid bound at general positive $n$; the main code need not be random or a product code. Condition 4 means that the seed-independent $C_1$ has $\Pr\{x\in C_2(X)\}\le L/|C_1|$ for each nonzero $x\in C_1$, with $|C_2(X)|=L$ always. Each uniform coset key is encoded uniformly on its coset; leakage includes the public seed.
-- source:
--   Tight exponential analysis of universally composable privacy amplification and its applications, arXiv:1010.1358v5, PDF p. 16, General additive linear coding secrecy (92)–(94)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P28

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology

namespace QAlgorithms.Papers.Independent.Advance50.P28

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Hayashi, PDF p.16, (92)–(94): actual iid joint additive noise, public seed,
and arbitrary fixed block subcode. The case n=1 retains the one-shot bounds. -/
theorem general_additive_linear_secrecy {G E S : Type*} [AddCommGroup G] [Fintype G]
    [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableSpace E]
    [Fintype S] [Nonempty S] (mu : Measure E) [IsProbabilityMeasure mu]
    (p : E → G → ℝ) (hp : IsConditionalLaw p)
    (n L : ℕ) (hn : 0 < n) (hL : 0 < L)
    (C1 : AddSubgroup (Fin n → G)) (H : S → AddSubgroup C1) (w : S → ℝ)
    (hcond : SubcodeCondition C1 H w L) (R : ℝ)
    (hsize : (L : ℝ) = Real.exp ((n : ℝ) * R)) :
    (∀ t ∈ Set.Ioo (0 : ℝ) (1 / 2), expectedCosetLeakage
      (Measure.pi (fun _ : Fin n => Measure.count.prod mu))
      (blockDensity (generalAdditiveDensity p) n) C1 H w ≤
        3 * ENNReal.ofReal (Real.exp ((n : ℝ) *
          (t * Real.log (Fintype.card G : ℝ) + conditionalPhi mu p t))) /
          (L : ℝ≥0∞) ^ t) ∧
    expectedCosetLeakage (Measure.pi (fun _ : Fin n => Measure.count.prod mu))
      (blockDensity (generalAdditiveDensity p) n) C1 H w ≤
        3 * ENNReal.ofReal (Real.exp (-(n : ℝ) *
          conditionalPhiExponent mu p (Real.log (Fintype.card G : ℝ) - R))) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P28

end
