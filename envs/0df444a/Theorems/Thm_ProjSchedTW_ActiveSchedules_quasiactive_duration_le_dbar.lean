-- Prove2me | Theorems.Thm_ProjSchedTW_ActiveSchedules_quasiactive_duration_le_dbar
-- name    : ProjSchedTW.ActiveSchedules.quasiactive_duration_le_dbar
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T16:06:19.440183+00:00
-- url     : https://prove2.me/theorems/277613e8-0133-4f65-92c6-afc0b40fc42d
-- title:
--   Proposition 2.10.2 — every quasiactive schedule has project duration at most d̄
-- statement:
--   Let
--   $$\bar d=\sum_{i\in V}\max\Bigl(p_i,\ \max_{\langle i,j\rangle\in E}\delta_{ij}\Bigr).$$
--   Then $\bar d$ bounds the project duration of every quasiactive schedule:
--   $$S_{n+1}\le\bar d\qquad\text{for all } S\in\mathcal{QAS}.$$
--
--   Since an optimal schedule can be chosen active and thus quasiactive (Remark 2.4.10 (a)), $\bar d$ bounds the length of the planning horizon that any algorithm for $PS|temp|C_{\max}$ or $PS|temp|reg$ has to consider.
--
--   **Formalization Note** For a node $i$ with no outgoing arc in $E$ the inner maximum is over the empty set; the summand is then $p_i$.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, DOI 10.1007/978-3-540-24800-2, p. 117, Proposition 2.10.2 (proof p. 118)

import Mathlib
import Definitions.Def_ProjSchedTW_ActiveSchedules_Project
import Definitions.Def_ProjSchedTW_ActiveSchedules_Shifts

namespace ProjSchedTW.ActiveSchedules

/-- Proposition 2.10.2 (p. 117): `d̄ = ∑_{i ∈ V} max(p_i, max_{⟨i,j⟩ ∈ E} δ_ij)` bounds the
project duration of every quasiactive schedule: `S_{n+1} ≤ d̄` for all `S ∈ QAS`. -/
theorem quasiactive_duration_le_dbar {n : ℕ} {K : Type} (P : Project n K)
    (S : Fin (n + 2) → ℝ) (hS : IsQuasiactive P S) :
    S (Fin.last (n + 1)) ≤ (dbar P : ℝ) := by sorry

end ProjSchedTW.ActiveSchedules
