-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P48_effectiveChargeWeights
-- name    : QAlgorithms.Papers.Independent.Intake100.P48.effectiveChargeWeights
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:23:59.732519+00:00
-- url     : https://prove2.me/theorems/b34fc36d-967b-4e57-87b6-8690e4ba8064
-- title:
--   Effective puncture weights and quantum-trace fusion probabilities
-- statement:
--   Let $\mathcal A$ be a finite set of sectors with vacuum $1$, involutive conjugation $a\mapsto\bar a$, and commutative, associative, rigid fusion multiplicities $N_{ab}^{c}\in\mathbb N$. Let $d_a>0$ be their positive dimension character, with $d_1=1$, $d_{\bar a}=d_a$, and $\sum_cN_{ab}^{c}d_c=d_ad_b$. Put $D=(\sum_a d_a^2)^{1/2}$. The canonical vacuum-cycle vector has charge coordinates $d_a/D$; define $p_a$ by the Born rule. Define fusion probabilities by normalized quantum traces of the outgoing-charge projectors: each basis state with outgoing charge $c$ has quantum-trace weight $d_c$. For three inputs retain both multiplicity labels and the intermediate fusion channel. Define $N_{abc}=N_{ab}^{\bar c}$ and $N_{abcd}=\sum_xN_{ab}^{x}N_{xc}^{\bar d}$.
--
--   Then $D>0$, all these conditional laws are normalized, and
--
--   $$
--   p_a=\frac{d_a^2}{D^2},\qquad p_{ab\to\bar c}=\frac{N_{abc}d_c}{d_ad_b},\qquad
--   p_{abc\to\bar d}=\frac{N_{abcd}d_d}{d_ad_bd_c},
--   $$
--   $$
--   p_{abc}:=p_ap_b p_{ab\to\bar c}=\frac{N_{abc}d_ad_bd_c}{D^4},\qquad
--   p_{abcd}:=p_ap_bp_c p_{abc\to\bar d}=\frac{N_{abcd}d_ad_bd_cd_d}{D^6}.
--   $$
--
--   The two joint laws each sum to one. These are effective charge experiments; no claim identifies an unspecified microscopic marginal with either law.
-- source:
--   Topological entanglement entropy, arXiv:hep-th/0510092v2, PDF p. 3, Eqs. (9)–(11), (13)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P48

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P48

open Filter

open scoped Topology ComplexConjugate

attribute [local instance] Classical.propDecidable

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- PDF p.3, (9)–(11),(13): effective charge weights and quantum-trace fusion
probabilities. Vacuum multiplicity uses outgoing bar(c), not c. The constructed
laws are normalized; they are not assumptions about microscopic reduced states. -/
theorem effectiveChargeWeights (f : FusionData A) :
    0 < totalDimension f.dim ∧
    (∑ a, punctureProbability f a) = 1 ∧
    (∀ a, punctureProbability f a = f.dim a ^ 2 / totalDimension f.dim ^ 2) ∧
    (∀ a b, (∑ c, fusionProbability f a b c) = 1 ∧
      ∀ c, fusionProbability f a b (f.dual c) =
        (vacuumMultiplicityThree f a b c : ℝ) * f.dim c / (f.dim a * f.dim b)) ∧
    (∀ a b c, (∑ d, tripleFusionProbability f a b c d) = 1 ∧
      ∀ d, tripleFusionProbability f a b c (f.dual d) =
        (vacuumMultiplicityFour f a b c d : ℝ) * f.dim d /
          (f.dim a * f.dim b * f.dim c)) ∧
    (∑ a, ∑ b, ∑ c, jointThree f a b c) = 1 ∧
    (∀ a b c, jointThree f a b c =
      (vacuumMultiplicityThree f a b c : ℝ) * f.dim a * f.dim b * f.dim c /
        totalDimension f.dim ^ 4) ∧
    (∑ a, ∑ b, ∑ c, ∑ d, jointFour f a b c d) = 1 ∧
    (∀ a b c d, jointFour f a b c d =
      (vacuumMultiplicityFour f a b c d : ℝ) *
        f.dim a * f.dim b * f.dim c * f.dim d / totalDimension f.dim ^ 6) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P48

end
