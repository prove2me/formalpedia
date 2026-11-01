-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P63_optimized_accessible_additivity
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P63.optimized_accessible_additivity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:14:10.812541+00:00
-- url     : https://prove2.me/theorems/e6cce99f-1207-4e7c-ad25-8a5bad7ef5e2
-- title:
--   Additivity of optimized accessible equivocation
-- statement:
--   Let $(\rho_i)_{i\in I}$ and $(\sigma_k)_{k\in K}$ be normalized density matrices on nonzero finite-dimensional spaces $E$ and $F$, where $I$ and $K$ are finite nonempty label sets. These are the output families of two cq-channels. For any family $\tau$ and prior $p$, write $S_{\rm acc}(p;\tau)=\min_Q H(X|J)$, with joint probabilities $p_x\operatorname{Tr}(\tau_xQ_j)$ and arbitrary finite POVMs. Then
--
--   $$\max_{p_{ik}}S_{\rm acc}(p_{ik};\rho_i\otimes\sigma_k)=\max_{p_i}S_{\rm acc}(p_i;\rho_i)+\max_{p_k}S_{\rm acc}(p_k;\sigma_k).$$
--
--   The left optimization includes every correlated joint prior, and Eve may measure $E\otimes F$ jointly. Zero prior weights are allowed. This is the additivity statement for complements of cq-channels, expressed directly through their cq output families; all logarithms are binary.
-- source:
--   Weak locking capacity of quantum channels can be much larger than private capacity, arXiv:1403.6361v3, PDF p. 7, Lemma 4: additivity of optimized accessible equivocation

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P63

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P63

open QAlgorithms Filter

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Information100.P04 (Measurement)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon labelInformation)

open QAlgorithms.Papers.Independent.Information100.P71 (channelPower dilationMap SupportIncluded)

open QAlgorithms.Papers.Independent.Bridge50.P47 (SymmetricIndex universalSymmetricDilation)

open QAlgorithms.Learning (IsDistribution)

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.7–8, Lemma 4: all correlated priors and all joint POVMs are allowed.
Every normalized state family is the output family of a cq-channel. -/
theorem optimized_accessible_additivity {I K E F : Type}
    [Fintype I] [Nonempty I] [Fintype K] [Nonempty K]
    [Fintype E] [DecidableEq E] [Nonempty E]
    [Fintype F] [DecidableEq F] [Nonempty F]
    (rho : I → Mat E) (sigma : K → Mat F)
    (hrho : ∀ i, IsDensityMatrix (rho i)) (hsigma : ∀ k, IsDensityMatrix (sigma k)) :
    optimizedEquivocation (fun x : I × K => Matrix.kronecker (rho x.1) (sigma x.2)) =
      optimizedEquivocation rho + optimizedEquivocation sigma := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P63

end
