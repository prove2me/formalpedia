-- Prove2me | Theorems.Thm_TwoAgentSched_TotalTotal_totalTotal_encoding_reduction
-- name    : TwoAgentSched.TotalTotal.totalTotal_encoding_reduction
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-27T06:40:51.834171+00:00
-- url     : https://prove2.me/theorems/7a8c7728-5e47-4f11-9598-7e0b07dfbc51
-- title:
--   Theorem 9.2 — Polynomial-Time Binary Encoding Reduction for Two-Agent Total Completion Time
-- statement:
--   There exists a polynomial-time computable function $f$ on $\mathrm{BSym}$ strings that reduces $\mathrm{partitionLang}$ to $\mathrm{targetLang}$ via strictly increasing instance data $p : \mathrm{Fin}\;k \to \mathbb{N}$ and the two-agent instance $\mathrm{construction}(p)$ with threshold $Q_A = Q_B = \mathrm{thresholdQ}(p)$.
-- source:
--   Agnetis, Mirchandani, Pacciarelli & Pacifici 2004, Scheduling problems with two competing agents, Operations Research 52(2), pp. 237–238, Theorem 9.2

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Set.Card
import Mathlib.Data.List.Sort
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_TwoAgentSched_TotalTotal_Construction

namespace TwoAgentSched.TotalTotal

open CookPvsNP ProjSchedTW.Complexity

/-- Polynomial-time binary encoding reduction for Theorem 9.2 (Agnetis et al. 2004, pp. 237–238):
there is a polynomial-time computable reduction `f` on `BSym` strings that reduces `partitionLang`
to `targetLang` via strictly increasing instance data `p : Fin k → ℕ` and the constructed two-agent
instance `construction p` with threshold `thresholdQ p`. -/
theorem totalTotal_encoding_reduction :
    ∃ f : List BSym → List BSym, PolyTimeComputable f ∧
      ∀ x : List BSym,
        ∃ (k : ℕ) (p : Fin k → ℕ), StrictMono p ∧
          (x ∈ partitionLang ↔ PartitionYes (List.ofFn p)) ∧
          ((construction p).RecYes (thresholdQ p) (thresholdQ p) ↔ f x ∈ targetLang) := by sorry

end TwoAgentSched.TotalTotal
