-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P19_limit_one
-- name    : QAlgorithms.Papers.Independent.Support50.P19.limit_one
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:31:56.113227+00:00
-- url     : https://prove2.me/theorems/fce1e627-242e-4a16-bdd3-efa3753497ef
-- title:
--   Right-hand limit at order one
-- statement:
--   Let $A\ge0$ have trace one on a nonzero finite complex space, and let $B\ge0$ be arbitrary on that space. With base-two logarithms,
--   $$\lim_{\alpha\downarrow1}\widetilde D_\alpha(A\Vert B)=D(A\Vert B).$$
--   Here $D(A\Vert B)=\operatorname{Tr}[A\log_2A-A\log_2B]$ on support inclusion and is $+\infty$ otherwise. The limit is in the extended real topology. The right-hand direction matches the paper's domain $\alpha>1$ and includes unsupported pairs; it connects the new divergence to ordinary relative entropy.
-- source:
--   Strong converse for the classical capacity of entanglement-breaking and Hadamard channels via a sandwiched Renyi relative entropy, arXiv:1306.1586v4, PDF p. 15, proposition11

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P19

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate ENNReal

open Filter Topology

namespace QAlgorithms.Papers.Independent.Support50.P19

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P35
  (tr Dominates spectralPower elog elogNN rawTrace cq)

open QAlgorithms.Papers.Independent.Dependency50.P09 (sandwichedD petzD relativeD)

open QAlgorithms.Papers.Independent.Information100.P56 (sandwichedTrace)

open QAlgorithms.Papers.Independent.Information100.P27 (average)

open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel)

open QAlgorithms.Papers.Independent.Claimed50.P48 (FiniteKrausCP)

open QAlgorithms.Papers.Independent.Dependency50.P23
  (UACode uaCodeSuccess ordinaryClassicalCapacity IsEB IsHadamard)

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble)

open QAlgorithms.Papers.Independent.Information100.P71 (channelPower)

open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

open QAlgorithms.Papers.Independent.Claimed50.P26
  (CovariantIrreducible minOutput UnassistedExponentialConverse)

variable {I J K L : Type} [Fintype I] [Fintype J] [Fintype K] [Fintype L]

variable [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq L]

/-- PDF pp.15–17, Proposition 11: the right limit at one, with no support restriction on B. -/
theorem limit_one [Nonempty I] (A : {X : Matrix I I ℂ // IsDensityMatrix X}) (B : Matrix I I ℂ) (hB : B.PosSemidef) :
    Tendsto (fun a : ℝ => sandwichedD a A.1 B) (nhdsWithin 1 (Set.Ioi 1))
      (nhds (relativeD A.1 B)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P19

end
