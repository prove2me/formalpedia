-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P36_erasureLockingBound
-- name    : QAlgorithms.Papers.Independent.Bridge50.P36.erasureLockingBound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:16:33.044321+00:00
-- url     : https://prove2.me/theorems/65c98c3a-f361-4b65-830b-eee63238eb02
-- title:
--   One-use locking-information bound for the erasure channel
-- statement:
--   Let $d\ge1$ be an integer and $0\le p\le\tfrac12$. Let $\mathcal E_{p,d}(\rho)=(1-p)\rho\oplus p|e\rangle\langle e|$, where the pure erasure flag is orthogonal to the $d$-dimensional input. Define $\gamma_d=\ln d-\sum_{t=2}^{d}1/t$. Then
--
--   $$
--   L_u^{(1)}(\mathcal E_{p,d})\le(1-p)\log_2 d-p\gamma_d\log_2 e.
--   $$
--
--   The locking information is the supremum of $I(X;B)-I_{\rm acc}(X;E)$ over normalized finite ensembles of possibly mixed inputs. Accessible information optimizes over all POVMs on the full complementary output, using that same ensemble. This is a single-use upper bound in bits.
--
--   The finite-dimensional correction improves the trivial Holevo upper bound. The separately inventoried printed limiting assertion is false and is deferred; it is not part of this theorem.
-- source:
--   Superadditivity of private information for any number of uses of the channel, arXiv:1502.05326v1, PDF p. 3, Lemma 2, (17)

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P36

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P36

open scoped BigOperators Matrix ComplexConjugate

open MeasureTheory

-- These imports are pinned accepted libraries, permitted by the repair task.
-- P08.Ensemble allows an impossible zero-sized normalized ensemble; its total=1
-- field excludes that case without a separate positive-size field.

open QAlgorithms.Papers.Independent.Information100.P08
  (Ensemble ensembleAverage outputHolevo channelHolevo)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)

open QAlgorithms.Papers.Independent.Information100.P67
  (receiverChannel complementaryChannel maximumCoherentInformation dilationPower erasureDilation)

open QAlgorithms.Papers.Independent.Dependency50.P07 (accessibleInformation)

open QAlgorithms.Papers.Independent.Dependency50.P48 (privateMaximum)

variable {A B E C D : Type}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype E] [DecidableEq E] [Fintype C] [DecidableEq C]

variable [Fintype D] [DecidableEq D]

/-- Lemma 2, PDF p.3 (17): one-use locking bound with the literal sum
through d. The false appended limit is separately deferred. -/
theorem erasureLockingBound (d : ℕ) (hd : 0 < d) (p : ℝ)
    (hp0 : 0 ≤ p) (hpHalf : p ≤ 1 / 2) :
    lockingInformation (erasureDilation (A := Fin d) p) ≤
      (1 - p) * Real.logb 2 (d : ℝ) - p * gammaValue d * Real.logb 2 (Real.exp 1) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P36

end
