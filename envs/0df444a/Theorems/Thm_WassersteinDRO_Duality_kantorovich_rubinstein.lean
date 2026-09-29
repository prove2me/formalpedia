-- Prove2me | Theorems.Thm_WassersteinDRO_Duality_kantorovich_rubinstein
-- name    : WassersteinDRO.Duality.kantorovich_rubinstein
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-21T02:18:28.681975+00:00
-- url     : https://prove2.me/theorems/c94176b8-0f5c-4c1a-87ab-8484330e406a
-- title:
--   Theorem 2 — Kantorovich-Rubinstein theorem
-- statement:
--   The type-1 Wasserstein distance between two Borel probability measures $Q, Q'$ on $E$
--   admits the dual representation
--   $$W_1(Q,Q') = \sup_{\mathrm{Lip}(\varphi)\le 1} \int_E \varphi\,dQ - \int_E \varphi\,dQ',$$
--   the supremum ranging over real-valued functions $\varphi$ with Lipschitz modulus at most
--   $1$ that are integrable under both $Q$ and $Q'$. Both sides are compared in the extended
--   reals for the same reason as Theorem 1. The paper attributes the compactly-supported case
--   to Kantorovich and Rubinstein and the general case to Villani, [108, Remark 6.5].
-- source:
--   Kuhn et al. 2019, Theorem 2, p. 4, citing Kantorovich & Rubinstein [51] (compactly supported case) and Villani, Optimal Transport: Old and New, [108, Remark 6.5] (general case)

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_wassersteinDistance
import Definitions.Def_WassersteinDRO_Duality_lipschitzModulus

open MeasureTheory

namespace WassersteinDRO.Duality

/-- Theorem 2 (Kantorovich-Rubinstein theorem), Kuhn et al. 2019, p. 4: the type-1
Wasserstein distance between `Q` and `Q'` admits the dual representation
`W1(Q,Q') = sup_{Lip(φ)≤1} ∫φ dQ - ∫φ dQ'`. The `Integrable` guards on `φ` under `Q` and
`Q'` make the two Bochner integrals meaningful for every candidate `φ` in the supremum,
rather than relying on Mathlib's junk value `0` for a non-integrable integrand; both sides
are cast to `EReal` for the same reason as in Theorem 1. -/
theorem kantorovich_rubinstein {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [BorelSpace E] [SecondCountableTopology E]
    (Q Q' : Measure E) [IsProbabilityMeasure Q] [IsProbabilityMeasure Q'] :
    ((wassersteinDistance 1 Q Q' : ENNReal) : EReal) =
      ⨆ (φ : E → ℝ) (_ : lipschitzModulus φ ≤ 1)
        (_ : Integrable φ Q) (_ : Integrable φ Q'),
        ((∫ x, φ x ∂Q - ∫ x, φ x ∂Q' : ℝ) : EReal) := by sorry

end WassersteinDRO.Duality
