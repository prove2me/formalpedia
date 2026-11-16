-- Prove2me | Theorems.Thm_SuperactivatedCheating_StateConversion_Supplement_theorem_28
-- name    : SuperactivatedCheating.StateConversion.Supplement.theorem_28
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:24:47.847754+00:00
-- url     : https://prove2.me/theorems/a5ab9c62-afc3-4259-8007-674724dc8411
-- title:
--   Theorem 28 (companion theorem; not used in the proof of the goal) — perfect square and cube
-- statement:
--   There exists a finite two-round QMIP protocol $G$ with a valid verifier circuit such that
--   $$\omega(G)<1,\qquad\omega(G^3)=\omega(G^2)=1.$$
--   The local value ranges over product initial resources and all finite retained memories and local CPTP operations. Repeated protocols use independent verifier copies and arbitrary joint local prover operations. This is the paper’s multi-round classical-message companion to the published one-round goal; external channel superactivation facts remain proof obligations, not hypotheses.
--
--   Differences from the source:
--   - encoding: a QMIP protocol with square and cube values one → a valid concrete finite two-round verifier circuit with all local finite memories; reason: the source witness is such a circuit; both repeated values are computed from independent verifier copies
--   - encoding: finite-dimensional registers and CPTP operations → finite types in Type 0 with decidable equality, coordinate matrices and the published finite normalized Kraus channel predicate; reason: every finite register and every finite-dimensional CPTP map has this representation; no dimension or rank bound is imposed
--   - encoding: trace winning probabilities and local or assisted supremum values → real parts of accepting traces and real suprema over actual strategies; reason: on valid circuits the traces are real probabilities; the strategy sets are nonempty and bounded in [0,1], so no default supremum is used
--   - encoding: finite-dimensional prior shared states and local private resources → unit pure shared states and arbitrary finite retained memories; local resources are product pure states; reason: mixed resources can be purified locally without changing probabilities; every private dimension is represented by Fin e, and shared randomization cannot improve a supremum
--   - encoding: verifier sampling with private classical information or retained verification copies → the averaged initial density with a retained message or copy register, and local CPTP strategies on the received quantum registers; reason: averaging and a referee-held purification preserve all acceptance probabilities; the sampled classical description is not supplied in Hseq
-- source:
--   Bhattacharyya, Mančinska, Zhao, Quantum interaction can superactivate cheating under parallel repetition, STOC 2027 submission #399 (October 2026), Theorem 28, p. 24.

import Definitions.Def_SuperactivatedCheating_StateConversion_Supplement_Protocols

open scoped ENNReal NNReal Matrix
noncomputable section

namespace SuperactivatedCheating.StateConversion.Supplement

/-- Theorem 28, p.24: unconditional genuine QMIP protocol; both square and cube. -/
theorem theorem_28 : ∃ G : Protocol, G.Valid ∧ G.localValue < 1 ∧
    (G.rep 3).localValue = 1 ∧ (G.rep 2).localValue = 1 := by sorry

end SuperactivatedCheating.StateConversion.Supplement
