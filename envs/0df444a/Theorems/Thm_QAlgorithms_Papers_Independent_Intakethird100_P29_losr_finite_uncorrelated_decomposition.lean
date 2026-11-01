-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P29_losr_finite_uncorrelated_decomposition
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P29.losr_finite_uncorrelated_decomposition
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:12:29.657494+00:00
-- url     : https://prove2.me/theorems/3100d8d6-24f1-4086-bacb-7b293d631bf0
-- title:
--   Lemma 13 (G3): decomposition of LOSR into UCLOSR mixtures
-- statement:
--   All Bell scenarios have independent finite, nonempty Alice and Bob input and output alphabets. A behavior is a nonnegative conditional output law normalized at every input pair; $\mathrm{NS}$ imposes both no-signaling marginal identities. Processing uses one initial box with rules and randomness fixed independently of the supplied behavior. For every LOSR operation $W$, there are a positive integer $n$, nonnegative weights $w_1,\ldots,w_n$ summing to one, and UCLOSR operations $U_1,\ldots,U_n$ such that, simultaneously for every input behavior,
--
--   $$W(P)=\sum_{k=1}^n w_k U_k(P).$$
--
--   The weights and operations are independent of $P$. This is a decomposition of an operation, and includes the finite reduction of the accepted arbitrary-discrete shared-randomness interface.
-- source:
--   Nonlocality free wirings and the distinguishability between Bell boxes, arXiv:1611.06932v2, PDF p. 15, Lemma 13 (G3)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P29

noncomputable section

open scoped BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Intakethird100.P29

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Advance50.P47
  (Box IsCorrelation IsNoSignaling HasLocalModel TwoLocalBoxes losrTransform
   correlationMixture)

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Dependency50.P47 (Law)

/-- PDF p.15, Lemma 13, (G3). This also asserts the finite reduction of the
accepted arbitrary-discrete two-local-box interface: finite seed size, weights,
and components are chosen before *all* raw behaviors simultaneously.
No finite-support assumption is made on the original shared-variable laws. -/
theorem losr_finite_uncorrelated_decomposition {s t : BellScenario}
    (w : BellOperation s t) (hw : IsLOSR w) :
    ∃ (n : ℕ) (_hn : 0 < n) (weights : Fin n → ℝ)
      (u : Fin n → UncorrelatedWiring s t),
      IsLaw weights ∧ ∀ p chi psi alpha beta,
        w p chi psi alpha beta =
          ∑ k, weights k * (u k).apply p chi psi alpha beta := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P29

end
