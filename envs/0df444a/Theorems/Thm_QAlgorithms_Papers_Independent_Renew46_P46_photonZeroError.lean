-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P46_photonZeroError
-- name    : QAlgorithms.Papers.Independent.Renew46.P46.photonZeroError
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T22:00:37.199983+00:00
-- url     : https://prove2.me/theorems/9c1955f1-af6d-4863-a635-53b7efb7b4e5
-- title:
--   §V: eventually zero error for the noiseless photon channel below capacity
-- statement:
--   For the full-Fock noiseless photon channel, let $E\ge0$ be finite, let the input $m\in\mathbb N$ produce $|m\rangle\langle m|$, and impose total photon cost at most $nE$ on every codeword. Let $R\ge0$ satisfy $R<h(E)$, where $h(E)=(E+1)\log(E+1)-E\log E$, and set $M_n=\max\{1,\lfloor e^{nR}\rfloor\}$. The constructed signals are density operators and exactly the number-state projectors. There is $n_0$ such that, for every positive $n\ge n_0$, an actual $M_n$-message collective-measurement code has zero uniform-message average error. Consequently,
--
--   $$p(n,M_n)=0\quad(n\ge n_0,\ n>0),\qquad \mathcal E(R)=+\infty.$$
--
--   The statement is eventual in blocklength. At $E=0$ there is no nonnegative strict-subcapacity rate.
-- source:
--   On Quantum Communication Channels with Constrained Inputs, arXiv:quant-ph/9705054v1, PDF p. 15, §V: eventually zero error for the noiseless photon channel below capacity

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P46

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P46

open Filter MeasureTheory QAlgorithms.RealRegisters

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Section V, PDF p.15: eventual zero-error attainment, not a claim at every
small blocklength. The photon cost is m on every word, N=0; R>=0 is strictly
below h(E). At E=0 this rate domain is empty, as in the source. -/
theorem photonZeroError (E R : ℝ) (hE : 0 ≤ E) (hR : 0 ≤ R) (hRC : R < h E) :
    ∃ hP : ∀ m, constrainedCqDensity (photonSignal 0 m),
      (∀ m, photonSignal 0 m = InnerProductSpace.rankOne ℂ (constrainedCqKet m) (constrainedCqKet m)) ∧
      (∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → 0 < n →
        (∃ c : constrainedCqCode (stateFamily (photonSignal 0) hP) (fun m : ℕ => (m : ℝ)) E n
          (constrainedCqMessages n R), constrainedCqCodeError c = 0) ∧
        constrainedCqError (stateFamily (photonSignal 0) hP) (fun m : ℕ => (m : ℝ)) E n
          (constrainedCqMessages n R) = 0) ∧
      reliability (stateFamily (photonSignal 0) hP) (fun m : ℕ => (m : ℝ)) E R = ⊤ := by sorry

end QAlgorithms.Papers.Independent.Renew46.P46

end
