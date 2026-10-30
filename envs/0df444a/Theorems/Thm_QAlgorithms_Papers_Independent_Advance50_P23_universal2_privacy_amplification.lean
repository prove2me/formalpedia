-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P23_universal2_privacy_amplification
-- name    : QAlgorithms.Papers.Independent.Advance50.P23.universal2_privacy_amplification
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:49:50.429997+00:00
-- url     : https://prove2.me/theorems/4ddab5c1-233a-47e4-a834-298451ace7db
-- title:
--   Universal2 privacy amplification with two spectral bounds
-- statement:
--   Let $P_A$ be a law, $W_a$ normalized finite Eve states, $P_Z$ a seed law, and $f_z:A\to D$ universal2, with $|D|>0$. Define $d_z=\sum_d\|\sum_{a:f_z(a)=d}P_A(a)W_a-\bar W/|D|\|_1$ and $H=-D_s(W\times P_A\|\sigma_E\otimes I_A)$ for any normalized reference $\sigma_E$ and $0<s\le1$. Then $\mathbb E d_z\le(4+\sqrt v)|D|^{s/2}e^{-sH/2}$ and $\mathbb E d_z\le(4+\sqrt{\lceil\lambda\rceil})|D|^{s/2}e^{-sH/2+s/2}$, where $v$ counts distinct eigenvalues and $\lambda$ is logarithmic spread on the positive reference support. The common comparison marginal is $\bar W=\sum_aP_A(a)W_a$. Full trace norm and natural logarithms are used. Support failure yields an infinite upper bound.
-- source:
--   Quantum wiretap channel with non-uniform random number and its exponent and equivocation rate of leaked information, arXiv:1202.0325v3, PDF p. 30, Lemma 14, (175)–(176): universal2 privacy amplification

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P23

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P23

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal

open Filter

open QAlgorithms.Papers.Independent.Information100.P56
  (IsLaw entropy average holevo uniform ProjectiveRep orbit productOutput)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Dependency50.P21 (IsSupported relativeEntropy)

open QAlgorithms.Papers.Independent.Dependency50.P28 (pinch logNonnegativeExtended)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {X A Z B E : Type} [Fintype X] [Fintype A] [Fintype Z]
  [Fintype B] [DecidableEq B] [Fintype E] [DecidableEq E]

/-- PDF p.30, Lemma 14, (175)–(176), cited to [18,Lemma 33]. Both spectral
bounds apply to the same universal2 law and every normalized reference. Support
failure has an infinite RHS, rather than a total-real logarithm default. -/
theorem universal2_privacy_amplification {D : Type} [Fintype D] [Nonempty D]
    [Nonempty A] [Nonempty E]
    (W : A → Matrix E E ℂ) (hW : hayashiIsCQ W) (PA : A → ℝ) (hPA : IsLaw PA)
    (PZ : Z → ℝ) (hPZ : IsLaw PZ) (f : Z → A → D) (hf : Universal2 PZ f)
    (sigma : Matrix E E ℂ) (hsigma : IsDensityMatrix sigma)
    (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) :
    ENNReal.ofReal (∑ z, PZ z * hashedDistance W PA (f z)) ≤
      ENNReal.ofReal ((4 + Real.sqrt (eigenCount sigma)) * Real.rpow (Fintype.card D) (s / 2)) *
        EReal.exp (-((s / 2 : ℝ) : EReal) * conditionalRenyiReference s W PA sigma) ∧
    ENNReal.ofReal (∑ z, PZ z * hashedDistance W PA (f z)) ≤
      ENNReal.ofReal ((4 + Real.sqrt (Int.ceil (spectralSpread sigma))) *
        Real.rpow (Fintype.card D) (s / 2) * Real.exp (s / 2)) *
        EReal.exp (-((s / 2 : ℝ) : EReal) * conditionalRenyiReference s W PA sigma) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P23

end
