-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P28_additive_linear_secrecy
-- name    : QAlgorithms.Papers.Independent.Advance50.P28.additive_linear_secrecy
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:58:59.427094+00:00
-- url     : https://prove2.me/theorems/d70a5f05-0e0a-4e40-8ff5-a2bc3b5ccb8a
-- title:
--   Additive linear coding secrecy (88)–(91)
-- statement:
--   All logarithms are natural and $d_1$ is the full $L^1$ distance. Let $P$ be a normalized law on a finite nonempty alphabet $A$, and let $U_M$ be the uniform law on $M\ge1$ symbols. For a map $f$, write $f_*P$ for its pushforward. Let $A=G$ be a finite abelian group and use the iid additive noise channel on $G^n$, $n\ge1$. Fix any block subgroup $C_1$ and random size-$L$ subgroups $C_2(X)\le C_1$ obeying Condition 4. Suppose $L=e^{nR}$. For $0<t<1/2$,
--   $$\mathbb E_Xd_1\le3\frac{\exp(n[t\log|G|-tH_{1/(1-t)}(P)])}{L^t}$$
--   Optimization gives
--   $$\mathbb E_Xd_1\le3\exp\{-n e_H(P,\log|G|-R)\}.$$
--   Also $\exp\phi(t|W^n,U_{C_1})\le\exp\phi(t|W^n,U_{G^n})$ on $[0,1/2]$. The case $n=1$ is the one-shot assertion. The size equality restricts $R$ to actual subgroup sizes. For $s>0$, $H_{1+s}(P)=-s^{-1}\log\sum_aP(a)^{1+s}$, and $g(s)=sH_{1+s}(P)$ with $g(0)=0$. Condition 4 means that the seed-independent $C_1$ has $\Pr\{x\in C_2(X)\}\le L/|C_1|$ for each nonzero $x\in C_1$, with $|C_2(X)|=L$ always. Each uniform coset key is encoded uniformly on its coset; leakage includes the public seed. Write $e_H(P,u)=\max_{0\le s\le1}(g(s)-su)/(1+s)$ and $\widetilde e_H(P,u)=\max_{0\le s\le1}(g(s)-su)/2$.
-- source:
--   Tight exponential analysis of universally composable privacy amplification and its applications, arXiv:1010.1358v5, PDF p. 16, Additive linear coding secrecy (88)–(91)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P28

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology

namespace QAlgorithms.Papers.Independent.Advance50.P28

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Hayashi, PDF pp.15–16, (88)–(91): n=1 is (89)–(90), arbitrary positive n
is (91). The cardinality equality L=exp(nR) is a hypothesis, not rounding. -/
theorem additive_linear_secrecy {G S : Type*} [AddCommGroup G] [Fintype G]
    [MeasurableSpace G] [MeasurableSingletonClass G] [Fintype S] [Nonempty S]
    (P : G → ℝ) (hP : IsLaw P) (n L : ℕ) (hn : 0 < n) (hL : 0 < L)
    (C1 : AddSubgroup (Fin n → G)) (H : S → AddSubgroup C1) (w : S → ℝ)
    (hcond : SubcodeCondition C1 H w L) (R : ℝ)
    (hsize : (L : ℝ) = Real.exp ((n : ℝ) * R)) :
    (∀ t ∈ Set.Icc (0 : ℝ) (1 / 2),
      gallagerDensityMoment Measure.count (additiveDensity (iid P n)) (subgroupUniform C1) t ≤
        gallagerDensityMoment Measure.count (additiveDensity (iid P n)) (finiteUniformMass (Fin n → G)) t) ∧
    (∀ t ∈ Set.Ioo (0 : ℝ) (1 / 2),
      expectedCosetLeakage Measure.count (additiveDensity (iid P n)) C1 H w ≤
        3 * ENNReal.ofReal (Real.exp ((n : ℝ) *
          (t * Real.log (Fintype.card G : ℝ) - (1 - t) * renyiNumerator P (t / (1 - t))))) /
          (L : ℝ≥0∞) ^ t) ∧
    expectedCosetLeakage Measure.count (additiveDensity (iid P n)) C1 H w ≤
      3 * ENNReal.ofReal (Real.exp (-(n : ℝ) *
        directExponent P (Real.log (Fintype.card G : ℝ) - R))) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P28

end
