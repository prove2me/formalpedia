-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P22_classical_markovApproximation
-- name    : QAlgorithms.Papers.Independent.Gap48.P22.classical_markovApproximation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:17:21.04899+00:00
-- url     : https://prove2.me/theorems/f5b1378d-b1fd-431b-b703-87a7a754bad6
-- title:
--   Classical conditional information and its Markov approximation
-- statement:
--   Let $P$ be a discrete probability law on arbitrary alphabets $X,Y,Z$. Conditional laws are the usual normalized laws on positive-probability events; at a null event $Y=y$, take the unconditional marginal as completion. Define the Markov law on the same alphabets by $Q(x,y,z)=P_{XY}(x,y)P_{Z\mid Y}(z\mid y)$. If the conditional mutual information in bits is the finite real number $I_P(X:Z\mid Y)=\varepsilon\ge0$, then
--
--   $$I_Q(X:Z\mid Y)=0,\qquad D_2(P\|Q)=\varepsilon,\qquad\|P-Q\|_1\le\sqrt{2\ln2}\sqrt\varepsilon.$$
--
--   Here $D_2$ is extended relative entropy in bits, and the norm is the full sum of absolute mass differences. This identifies the precise Markov approximation and quantifies its proximity without a finite-alphabet or full-support assumption.
-- source:
--   Squashed entanglement, k-extendibility, quantum Markov chains, and recovery maps, arXiv:1410.4184v4, PDF p. 8, Lemma 1

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P22

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Gap48.P22

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P12 (squashedEntanglement KExtendible)

open QAlgorithms.Papers.Independent.Claimed50.P33
  (RegisterBasis registerMarginal entropyAt conditionalMultipartiteInformation singleParties
   forgetEnvironment)

open QAlgorithms.Papers.Independent.Renew46.P35 (classicalCMI)

open QAlgorithms.Entanglement (IsSeparableDensity)

/-- Lemma 1, PDF pp.8–9: the Markov law is constructed from P, including
null-event completion, and KL in bits is exactly epsilon. No finite alphabet assumption. -/
theorem classical_markovApproximation {X Y Z : Type*} (p : PMF (X × (Y × Z)))
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hinfo : classicalCMI p
      (conditionalLaw p (fun x => x.2.1) (fun x => (x.1,x.2.2))) = ENNReal.ofReal epsilon) :
    let q := markovApproximation p
    classicalCMI q (conditionalLaw q (fun x => x.2.1) (fun x => (x.1,x.2.2))) = 0 ∧
      discreteKL p q = ENNReal.ofReal epsilon ∧
      discreteL1 p q ≤ Real.sqrt (2 * Real.log 2) * Real.sqrt epsilon := by sorry

end QAlgorithms.Papers.Independent.Gap48.P22

end
