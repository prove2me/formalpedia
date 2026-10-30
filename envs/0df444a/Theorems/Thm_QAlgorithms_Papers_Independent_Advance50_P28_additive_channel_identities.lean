-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P28_additive_channel_identities
-- name    : QAlgorithms.Papers.Independent.Advance50.P28.additive_channel_identities
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:56:54.812244+00:00
-- url     : https://prove2.me/theorems/d2b4e3fc-a373-4932-9215-f50749e4fef0
-- title:
--   Additive-channel identities (80)–(81)
-- statement:
--   All logarithms are natural and $d_1$ is the full $L^1$ distance. Let $P$ be a normalized law on a finite nonempty alphabet $A$, and let $U_M$ be the uniform law on $M\ge1$ symbols. For a map $f$, write $f_*P$ for its pushforward. Now $A=G$ is a finite abelian additive group and $W_x(z)=P(z-x)$. For uniform channel input, $0\le t\le1/2$, and $s=t/(1-t)$,
--   $$\phi(t|W,U_G)=(1-t)\psi(s|W,U_G)=t\log|G|-tH_{1/(1-t)}(P).$$
--   At $t=0$ the entropy product means its zero continuous extension. For every real $R$, $e_\phi(W,U_G,R)=e_\psi(W,U_G,R)=e_H(P,\log|G|-R)$ and $\widetilde e_\psi(W,U_G,R)=\widetilde e_H(P,\log|G|-R)$, where $e_H(P,u)=\max_{0\le s\le1}(g(s)-su)/(1+s)$ and $\widetilde e_H(P,u)=\max_{0\le s\le1}(g(s)-su)/2$. These are full exponent identities. For $s>0$, $H_{1+s}(P)=-s^{-1}\log\sum_aP(a)^{1+s}$, and $g(s)=sH_{1+s}(P)$ with $g(0)=0$. The channel exponents mean $e_\phi(R)=\sup_{0\le t\le1/2}[tR-\phi(t)]$, $e_\psi(R)=\sup_{0\le s\le1}(sR-\psi(s))/(1+s)$ and $\widetilde e_\psi(R)=\sup_{0\le s\le1}(sR-\psi(s))/2$.
-- source:
--   Tight exponential analysis of universally composable privacy amplification and its applications, arXiv:1010.1358v5, PDF p. 15, Additive-channel identities (80)–(81)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P28

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology

namespace QAlgorithms.Papers.Independent.Advance50.P28

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Hayashi, PDF pp.14–15, (80)–(81): all additive-channel equalities. -/
theorem additive_channel_identities {G : Type*} [AddCommGroup G] [Fintype G]
    [MeasurableSpace G] [MeasurableSingletonClass G]
    (P : G → ℝ) (hP : IsLaw P) (R : ℝ) :
    (∀ t ∈ Set.Icc (0 : ℝ) (1 / 2),
      ENNReal.log (gallagerDensityMoment Measure.count (additiveDensity P) (finiteUniformMass G) t) =
        ((t * Real.log (Fintype.card G : ℝ) -
          (1 - t) * renyiNumerator P (t / (1 - t)) : ℝ) : EReal) ∧
      ((1 - t : ℝ) : EReal) * ENNReal.log
        (psiMoment Measure.count (additiveDensity P) (finiteUniformMass G) (t / (1 - t))) =
        ENNReal.log (gallagerDensityMoment Measure.count (additiveDensity P) (finiteUniformMass G) t)) ∧
    wiretapPhiExponent Measure.count (additiveDensity P) (finiteUniformMass G) R =
      (directExponent P (Real.log (Fintype.card G : ℝ) - R) : EReal) ∧
    wiretapPsiExponent Measure.count (additiveDensity P) (finiteUniformMass G) R =
      wiretapPhiExponent Measure.count (additiveDensity P) (finiteUniformMass G) R ∧
    wiretapTildeExponent Measure.count (additiveDensity P) (finiteUniformMass G) R =
      ((intrinsicExponent P (Real.log (Fintype.card G : ℝ) - R) / 2 : ℝ) : EReal) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P28

end
