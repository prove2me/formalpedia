-- Prove2me | Theorems.Thm_SteinitzExchange_Duality_Supplement_characteristic_criterion_corrected
-- name    : SteinitzExchange.Duality.Supplement.characteristic_criterion_corrected
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T04:36:23.19789+00:00
-- url     : https://prove2.me/theorems/ca74b5c0-815e-48ab-ad0d-946148dee08a
-- title:
--   Theorem 5.4 (corrected: equality with the concave closure on B)
-- statement:
--   Let $V$ be finite and nonempty, let $B\subseteq\mathbb Z^V$ be finite and nonempty with $B=\mathbb Z^V\cap\overline B$, and let $\omega:B\to\mathbb R$. The corrected characteristic-cone criterion is
--   $$\omega\text{ satisfies (EXC)}\quad\Longleftrightarrow\quad
--   \bigl[\omega=\widehat\omega\text{ on }B\bigr]\ \land\ \bigl[\operatorname{rec}\operatorname{Hyp}(\omega^\circ)\text{ is matroidal}\bigr]\ \land\ \bigl[\widehat L(\omega^\circ,p_0)\text{ is matroidal for every }p_0\bigr].$$
--   The characteristic cone is represented by the hypograph of the support minimum $\psi^\circ(p)=\min_{x\in B}\langle p,x\rangle$, as on p. 291. The localizations and matroidal functions are the published definitions of the local-supermodularity mission.
--
--   **Formalization Note.** The printed converse misses $\omega=\widehat\omega$ on $B$. The added condition excludes hidden values below the concave envelope, which conjugacy cannot detect. Lemma 4.5 supplies the forward equality; Theorems 4.4 and 5.1 with (5.12) support the converse after this restoration. The companion refutation gives a finite hole-free integral base set with both printed conditions but failing (EXC).
--
--   Differences from the source:
--   - correction: the two matroidality conditions alone are equivalent to (EXC) → the right-hand side also requires equality with the concave closure on B; reason: values below the envelope leave both conjugate conditions unchanged; the explicit three-point counterexample refutes the printed converse
-- source:
--   Murota, Convexity and Steinitz's Exchange Property, Adv. Math. 124 (1996), p. 293, Theorem 5.4

import Mathlib
import Definitions.Def_SteinitzExchange_Duality_IntegralBaseSet
import Definitions.Def_SteinitzExchange_Duality_Exchange
import Definitions.Def_SteinitzExchange_Duality_Conjugate
import Definitions.Def_SteinitzExchange_LocalSupermod_Matroidal
import Definitions.Def_SteinitzExchange_LocalSupermod_Localization

namespace SteinitzExchange.Duality.Supplement

/-- Theorem 5.4 (corrected): its two conjugate conditions cannot see values
strictly below the concave envelope. Restore equality with that envelope on B.
The forward equality is Lemma 4.5; the reverse follows from the integral
maximizer criterion of Theorem 4.4 and the local description (5.12).
The support minimum describes the characteristic cone by (5.7), p. 291. -/
theorem characteristic_criterion_corrected {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V] (B : Finset (V → ℤ)) (hB : B.Nonempty)
    (hhole : ∀ x : V → ℤ, x ∈ B ↔ toReal x ∈ hull B) (ω : (V → ℤ) → ℝ) :
    SatisfiesEXC B ω ↔
      (∀ x ∈ B, ω x = concaveClosure B ω (toReal x)) ∧
      SteinitzExchange.LocalSupermod.IsMatroidal
        (SteinitzExchange.LocalSupermod.supportMin B) ∧
      (∀ p₀ : V → ℝ, SteinitzExchange.LocalSupermod.IsMatroidal
        (SteinitzExchange.LocalSupermod.localization (concaveConj B ω) p₀)) := by sorry

end SteinitzExchange.Duality.Supplement
