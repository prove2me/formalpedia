-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P29_wpicc_normal_form
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P29.wpicc_normal_form
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:13:46.006026+00:00
-- url     : https://prove2.me/theorems/0219bfc5-afd4-4e17-9241-e04673973d8e
-- title:
--   Unnumbered main result: WPICC parametrisation (8), (A5)-(A6)
-- statement:
--   All Bell scenarios have independent finite, nonempty Alice and Bob input and output alphabets. A behavior is a nonnegative conditional output law normalized at every input pair; $\mathrm{NS}$ imposes both no-signaling marginal identities. Processing uses one initial box with rules and randomness fixed independently of the supplied behavior. For every operational WPICC wiring $W$ between two fixed scenarios there exist a real $0\le p\le1$, an LOSR wiring $V$, and a linear map $L$ on raw conditional arrays, with $L(P)\in\mathcal L$ for every $P\in\mathrm{NS}$, such that
--
--   $$W(P)=pL(P)+(1-p)V(P)\quad\text{for every }P\in\mathrm{NS}.$$
--
--   The same $p,V,L$ work for all inputs. This is a necessary normal form for the operational class, not a definition declaring arbitrary NS-to-local maps physically realizable. WPICC uses Appendix A’s fixed no-preparation LOSR branch and random adaptive preparation branches in which at least one party measures before the final inputs.
-- source:
--   Nonlocality free wirings and the distinguishability between Bell boxes, arXiv:1611.06932v2, PDF p. 4, Equation (8); Appendix A (A5)–(A6)

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

/-- PDF p.4, (8), derived in Appendix A, pp.10–11, (A5),(A6).
The weight, LOSR map, and linear NS-to-local map are uniform over the input.
There is no division by the weight, including when it equals zero. -/
theorem wpicc_normal_form {s t : BellScenario} (w : BellOperation s t)
    (hw : IsWPICC w) :
    ∃ (weight : ℝ), 0 ≤ weight ∧ weight ≤ 1 ∧
      ∃ (v : BellOperation s t) (l : Behavior s →ₗ[ℝ] Behavior t),
        IsLOSR v ∧ (∀ p, IsNS p → HasLocalModel (l p)) ∧
        ∀ p, IsNS p → w p = fun x y a b =>
          weight * l p x y a b + (1 - weight) * v p x y a b := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P29

end
