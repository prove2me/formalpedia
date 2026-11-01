-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P63_schur_subexponential_security
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P63.schur_subexponential_security
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:19:41.878368+00:00
-- url     : https://prove2.me/theorems/6a036840-328e-4d20-8f60-b88b188aa9ca
-- title:
--   Subexponentially vanishing weak-locking security error
-- statement:
--   Let $\mathcal N$ be a complement of a cq-channel, defined by a normalized fixed Stinespring isometry on nonzero finite-dimensional spaces with $\mathcal N^c(|i\rangle\langle j|)=\delta_{ij}\rho_i$. Choose any input prior $p$, and let $h=\widehat H(M)$ be the minimum output entropy of its associated POVM restricted to the average state's support. Let $(\eta_n)_{n\ge1}$ be any positive schedule with
--
--   $$\eta_n\longrightarrow0,\qquad \frac{-\log_2\eta_n}{n}\longrightarrow0.$$
--
--   There is a sequence of uniform-message codes with independent uniform preshared keys whose key bits per use tend to zero, whose limiting inferior communication rate is at least $h$, whose decoding error is zero, and whose full $\ell^1$ weak-locking error is at most $\eta_n$ for all sufficiently large $n$, uniformly over all finite environment POVMs.
--
--   This pins the source's slower-than-exponential error claim without asserting any fixed positive security exponent. The formal sequence index $n$ corresponds to block length $n+1$.
-- source:
--   Weak locking capacity of quantum channels can be much larger than private capacity, arXiv:1403.6361v3, PDF p. 11, Remark 11: subexponentially small weak-locking error

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

/-- PDF pp.10–11, Remark 11: any positive schedule tending to zero slower than
exponentially can be met at the same asymptotic rate, with o(n) secret bits. -/
theorem schur_subexponential_security {A B E : Type}
    [Fintype A] [DecidableEq A] [Nonempty A] [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype E] [DecidableEq E] [Nonempty E]
    (V : Matrix (B × E) A ℂ) (hV : Vᴴ * V = 1) (rho : A → Mat E)
    (hCq : CqComplement (environment V) rho) (p : A → ℝ) (hp : IsDistribution p)
    (etaSchedule : ℕ → ℝ) (heta : ∀ n, 0 < etaSchedule n)
    (hzero : Tendsto etaSchedule atTop (nhds 0))
    (hsub : Tendsto (fun n => -Real.logb 2 (etaSchedule n) / (n + 1)) atTop (nhds 0)) :
    ∃ C : (n : ℕ) → KeyedBlockCode A B (n + 1),
      Tendsto (fun n => keyRate (C n)) atTop (nhds 0) ∧
      KeyedRateAtLeast C (associatedMinimum p rho) ∧
      (∀ n, keyedAverageError (dilationMap V) (C n) = 0) ∧
      (∀ᶠ n in atTop, WeakSecure (environment V) (C n) (etaSchedule n)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P63

end
