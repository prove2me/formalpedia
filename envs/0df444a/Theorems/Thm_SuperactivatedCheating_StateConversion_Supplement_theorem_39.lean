-- Prove2me | Theorems.Thm_SuperactivatedCheating_StateConversion_Supplement_theorem_39
-- name    : SuperactivatedCheating.StateConversion.Supplement.theorem_39
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:28:21.658175+00:00
-- url     : https://prove2.me/theorems/d23f0b9c-cbc8-4850-92b4-2b4db13a5c6f
-- title:
--   Theorem 39 (companion theorem; not used in the proof of the goal) — three-message entangled-value monotonicity
-- statement:
--   Let $K,K'$ be arbitrary valid three-message QMIP protocols of Definition 38, not necessarily distinct. Their product is valid and
--   $$\omega^*(K\times K')\le\omega^*(K).$$
--   Each verifier applies an arbitrary joint CPTP map to the first messages and retains a reference register before the provers respond locally. The strategies include all finite prior entanglement and memories retained when sending the first messages, including correlations across the two copies. This excludes superactivated cheating for the full three-message class.
--
--   Differences from the source:
--   - encoding: all Definition 38 three-message protocols and their product → explicit valid joint verifier circuits and arbitrary finite retained private memories; product validity also concluded; reason: these are the source operations and all its allowed strategies, with register regrouping explicit
--   - encoding: finite-dimensional registers and CPTP operations → finite types in Type 0 with decidable equality, coordinate matrices and the published finite normalized Kraus channel predicate; reason: every finite register and every finite-dimensional CPTP map has this representation; no dimension or rank bound is imposed
--   - encoding: trace winning probabilities and local or assisted supremum values → real parts of accepting traces and real suprema over actual strategies; reason: on valid circuits the traces are real probabilities; the strategy sets are nonempty and bounded in [0,1], so no default supremum is used
--   - encoding: finite-dimensional prior shared states and local private resources → unit pure shared states and arbitrary finite retained memories; local resources are product pure states; reason: mixed resources can be purified locally without changing probabilities; every private dimension is represented by Fin e, and shared randomization cannot improve a supremum
-- source:
--   Bhattacharyya, Mančinska, Zhao, Quantum interaction can superactivate cheating under parallel repetition, STOC 2027 submission #399 (October 2026), Theorem 39, p. 27.

import Definitions.Def_SuperactivatedCheating_StateConversion_Supplement_ThreeMessage

open scoped ENNReal NNReal Matrix
noncomputable section

namespace SuperactivatedCheating.StateConversion.Supplement

/-- Theorem 39, p.27: full joint verifier channels and retained private memory. -/
theorem theorem_39 (K L : ThreeMessage) (hK : K.Valid) (hL : L.Valid) :
    (K.prod L).Valid ∧ (K.prod L).entangledValue ≤ K.entangledValue := by sorry

end SuperactivatedCheating.StateConversion.Supplement
