-- Prove2me | Theorems.Thm_SteinitzExchange_Duality_Supplement_characteristic_criterion_refuted
-- name    : SteinitzExchange.Duality.Supplement.characteristic_criterion_refuted
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T04:37:23.073077+00:00
-- url     : https://prove2.me/theorems/78d45aeb-6e8f-4be4-949b-8bb5c0b1afe4
-- title:
--   Theorem 5.4 (corrected: explicit refutation of the printed converse)
-- statement:
--   For $B=\{(2,0),(1,1),(0,2)\}$ and $\omega=(0,-10,0)$, $B$ is a finite integral base set with $B=\mathbb Z^2\cap\overline B$, and
--   $$\omega^\circ(p)=2\min(p_1,p_2).$$
--   Its characteristic cone is matroidal and every localization of $\omega^\circ$ is matroidal, but $\omega$ fails (EXC). Indeed the exchange between $(2,0)$ and $(0,2)$ would demand $0\le-20$. The localizations are $2p_1$, $2p_2$, or $2\min(p_1,p_2)$, according to the order of the coordinates of the base point. This is a refutation within all assumptions of printed Theorem 5.4.
--
--   **Formalization Note.** The cone is expressed by its support-minimum hypograph, as on p. 291. The total functions are used only on $B$. The finite example is an explicit refutation, alongside the full corrected criterion.
--
--   Differences from the source:
--   - correction: both printed matroidality conditions imply (EXC) → a concrete hole-free integral base set satisfies both conditions but fails (EXC); reason: the middle value is below the envelope and does not affect the conjugate
-- source:
--   Murota, Convexity and Steinitz's Exchange Property, Adv. Math. 124 (1996), p. 293, Theorem 5.4

import Mathlib
import Definitions.Def_SteinitzExchange_Duality_IntegralBaseSet
import Definitions.Def_SteinitzExchange_Duality_Exchange
import Definitions.Def_SteinitzExchange_Duality_Conjugate
import Definitions.Def_SteinitzExchange_LocalSupermod_Matroidal
import Definitions.Def_SteinitzExchange_LocalSupermod_Localization
import Definitions.Def_SteinitzExchange_Duality_Supplement_CharacteristicCounterexample

namespace SteinitzExchange.Duality.Supplement

/-- Refutation of the converse of printed Theorem 5.4, p. 293. The support
minimum's hypograph is the characteristic cone (p. 291). Both matroidality
conditions hold, on a nonempty hole-free integral base set, but (EXC) fails. -/
theorem characteristic_criterion_refuted :
    IsIntegralBaseSet characteristicBase ∧
    (∀ x : Fin 2 → ℤ, x ∈ characteristicBase ↔ toReal x ∈ hull characteristicBase) ∧
    (∀ p : Fin 2 → ℝ, concaveConj characteristicBase characteristicValue p =
      2 * min (p 0) (p 1)) ∧
    SteinitzExchange.LocalSupermod.IsMatroidal
      (SteinitzExchange.LocalSupermod.supportMin characteristicBase) ∧
    (∀ p₀ : Fin 2 → ℝ, SteinitzExchange.LocalSupermod.IsMatroidal
      (SteinitzExchange.LocalSupermod.localization
        (concaveConj characteristicBase characteristicValue) p₀)) ∧
    ¬ SatisfiesEXC characteristicBase characteristicValue := by sorry

end SteinitzExchange.Duality.Supplement
