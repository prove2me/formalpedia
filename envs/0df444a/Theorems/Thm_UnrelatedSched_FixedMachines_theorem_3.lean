-- Prove2me | Theorems.Thm_UnrelatedSched_FixedMachines_theorem_3
-- name    : UnrelatedSched.FixedMachines.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:40:34.563069+00:00
-- url     : https://prove2.me/theorems/c40f9a9f-62e5-45f8-8086-e28ecf8e3cbd
-- title:
--   Theorem 3 — enumerating long assignments and rounding the LP gives a $(1+\varepsilon)$-approximation for makespan
-- statement:
--   Let $m\ge 1$ machines and $n$ jobs be given, with a matrix $P=(p_{ij})$ of positive integer processing times, and let $\mathrm{OPT}$ be the minimum makespan over all schedules. Let $\varepsilon>0$ and let $V$ be any LP solver returning a vertex of each feasible residual LP (a vertex selector). Then the procedure $A_\varepsilon$ run with $V$ exists, and for every such procedure the binary search of Lemma 1 driven by it returns a schedule $\sigma$ with
--
--   $$
--   \mathrm{makespan}(\sigma) \le (1+\varepsilon)\,\mathrm{OPT}.
--   $$
--
--   The paper states: "Let $m$ be a fixed integer. There is a family $\{A_\varepsilon\}$ of algorithms such that, for each $\varepsilon>0$, $A_\varepsilon$ is a $(1+\varepsilon)$-approximation algorithm for the minimum makespan problem on $m$ unrelated parallel machines that requires time bounded by a polynomial in the input size and space bounded by a polynomial in $m$, $\log(1/\varepsilon)$, and the input size." Its proof establishes the approximation guarantee above for the algorithm it describes (enumerate long assignments, round a vertex of the residual LP, binary search on the deadline), which is what is formalized.
--
--   The result is a polynomial approximation scheme for every fixed number of machines whose space requirement is polynomial in $\log(1/\varepsilon)$, in contrast with the earlier scheme of Horowitz and Sahni.
--
--   **Formalization Note** The time and space bounds and the hypothesis that $m$ is fixed are not formalized; the guarantee is stated for every $m\ge 1$. The optimum is given by an optimal schedule $\sigma_{\mathrm{opt}}$. The output schedule is tied to the algorithm: it is produced by the binary search from answers of the procedure $A_\varepsilon$, each of which extends an admissible schedule of long assignments and rounds a vertex of the residual LP within its support.
-- source:
--   Lenstra, Shmoys, Tardos, Approximation algorithms for scheduling unrelated parallel machines, CWI Report OS-R8714 (1987), p. 6, Theorem 3

import Mathlib
import Definitions.Def_MatousekLP_Scheduling_Schedule
import Definitions.Def_UnrelatedSched_FixedMachines_LongAssignment
import Definitions.Def_UnrelatedSched_FixedMachines_BinarySearch

namespace UnrelatedSched.FixedMachines

open MatousekLP.Scheduling

/-- Theorem 3 (p. 6), as its proof establishes it: for every number `m ≥ 1` of machines, every
positive integer processing-time matrix `P`, every `ε > 0` and every LP solver `V`, the
procedure `A_ε` run with `V` exists, and the binary search of Lemma 1 driven by any such
procedure outputs a schedule whose makespan is at most `(1 + ε)` times the optimal makespan. -/
theorem theorem_3 {m n : ℕ} (hm : 0 < m) (P : Matrix (Fin m) (Fin n) ℕ)
    (hP : ∀ i j, 0 < P i j) (ε : ℝ) (hε : 0 < ε)
    (V : ℕ → (Fin n → Option (Fin m)) → Option (Matrix (Fin m) (Fin n) ℝ))
    (hV : IsVertexSelector P ε V) (σopt : Fin n → Fin m)
    (hopt : IsOptimalSchedule (fun i j => (P i j : ℝ)) σopt) :
    (∃ D : ℕ → Option (Fin n → Fin m), IsAepsProcedure P ε V D) ∧
    ∀ D : ℕ → Option (Fin n → Fin m), IsAepsProcedure P ε V D →
      makespan (fun i j => (P i j : ℝ)) (binarySearch hm P D) ≤
        (1 + ε) * makespan (fun i j => (P i j : ℝ)) σopt := by sorry

end UnrelatedSched.FixedMachines
