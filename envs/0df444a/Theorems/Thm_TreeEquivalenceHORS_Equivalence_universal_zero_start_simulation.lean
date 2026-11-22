-- Prove2me | Theorems.Thm_TreeEquivalenceHORS_Equivalence_universal_zero_start_simulation
-- name    : TreeEquivalenceHORS.Equivalence.universal_zero_start_simulation
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-21T19:00:42.383232+00:00
-- url     : https://prove2.me/theorems/5f90923c-c9f8-46a4-9672-0cfc2256a380
-- title:
--   Universal partial evaluation reduces to halting of zero-start two-counter programs
-- statement:
--   There is a total computable function mapping every program/input pair to a four-instruction-language two-counter machine started with both counters zero. The machine halts exactly when the partial-recursive program terminates on that input.
-- source:
--   Adapted from typh, DistLTLSynth.Char.section_3_2_minsky, Prove2Me submission 7bdcd522-de20-4ff2-8c23-66c7e4f87fd6 (Apache-2.0). The zero-start translation is new.

import Definitions.Def_TreeEquivalenceHORS_Equivalence_Machines

namespace TreeEquivalenceHORS.Equivalence

theorem universal_zero_start_simulation:
    ∃ m : ℕ → Machine, Computable (fun n => Encodable.encode (m n)) ∧
      ∀ n, (¬ (Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code n.unpair.1) n.unpair.2).Dom) ↔
        ¬ (m n).Halts := by sorry

end TreeEquivalenceHORS.Equivalence
