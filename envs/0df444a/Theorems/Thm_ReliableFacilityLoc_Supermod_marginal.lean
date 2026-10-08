-- Prove2me | Theorems.Thm_ReliableFacilityLoc_Supermod_marginal
-- name    : ReliableFacilityLoc.Supermod.marginal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:14:55.340546+00:00
-- url     : https://prove2.me/theorems/a4948780-a41d-4395-9063-627d2d1412c4
-- title:
--   A.3: the marginal cost $\Phi_i(S\cup\{v\}) - \Phi_i(S)$ of adding a facility
-- statement:
--   Assume $\lambda_i \ge 0$, $0 \le q_j < 1$ and $R \ge 1$. Let $S$ be a set of regular facilities, $v \notin S$ a regular facility with $|S| + 1 \le R$, and list $S$ as $j_1, \dots, j_n$ in nondecreasing order of distance. Let $\bar n$ and $t$ be the numbers of facilities of $S$ with $d_{ij} \le \varphi_i$, resp. $d_{ij} \le d_{iv}$, and $P_k$, $C_k$ as in the proof of Proposition 3.
--
--   1. If $d_{iv} \le \varphi_i$, then
--   $$
--   \Phi_i(S\cup\{v\}) - \Phi_i(S) = \lambda_i (1-q_v)\Big[P_t\, d_{iv} - \sum_{k=t+1}^{\bar n+1} C_k\Big] + \mu_{iv}.
--   $$
--   2. If $d_{iv} \ge \varphi_i$, then $\Phi_i(S\cup\{v\}) - \Phi_i(S) = \mu_{iv}$.
--
--   The new facility is inserted into the level-by-level assignment after the $t$ facilities that are at least as close; the formula records the resulting change in expected cost.
--
--   **Formalization Note** The paper treats only $d_{iv} < \varphi_i$, setting the other case aside "without loss of generality"; both cases are stated, and they agree at $d_{iv} = \varphi_i$. The hypothesis $|S| + 1 \le R$ is constraint (6c) for $S \cup \{v\}$.
-- source:
--   Cui, Ouyang, Shen, Reliable Facility Location Design under the Risk of Disruptions, UCTC-FR-2010-02 (Feb. 2010), p. 36 (PDF 38), Appendix A.3, second display

import Mathlib
import Definitions.Def_ReliableFacilityLoc_Supermod_RSP
import Definitions.Def_ReliableFacilityLoc_Supermod_ClosedForm

open Finset

namespace ReliableFacilityLoc.Supermod

/-- **Marginal cost of adding one facility** (Cui, Ouyang & Shen, UCTC-FR-2010-02 (Feb. 2010),
Appendix A.3, p. 36, PDF 38). Let `S` be a set of regular facilities, `v ∉ S` a regular facility
with `|S| + 1 ≤ R`, and `L = [j_1, …, j_n]` a list of `S` in nondecreasing order of distance;
let `n̄`, `t` be the numbers of elements of `S` with `d_ij ≤ φ_i`, resp. `d_ij ≤ d_iv`.
1. If `d_iv ≤ φ_i`, then
   `Φ_i(S ∪ {v}) − Φ_i(S) = λ_i (1 − q_v) [P_t d_iv − Σ_{k=t+1}^{n̄+1} C_k] + µ_iv`.
2. If `d_iv ≥ φ_i`, then `Φ_i(S ∪ {v}) − Φ_i(S) = µ_iv`.

Printed (p. 36): "Without loss of generality, we assume that diu and div are less than the penalty
cost φi, i.e. s ≤ n̄ and t ≤ n̄. It follows that Φi(S ∪ {v}) − Φi(S) = λi[Σ_{k=1}^{t} Ck +
Pt(1 − qv)div + qv Σ_{k=t+1}^{n̄+1} Ck] + Σ_{j∈S∪{v}} µij − λi Σ_{k=1}^{n̄+1} Ck − Σ_{j∈S} µij
= λi[Pt(1 − qv)div − (1 − qv) Σ_{k=t+1}^{n̄+1} Ck] + µiv = λi(1 − qv)[Ptdiv − Σ_{k=t+1}^{n̄+1} Ck] + µiv."

Formalization Note: part 1 is the printed formula, stated for `d_iv ≤ φ_i` (the printed "less
than" plus the boundary case, where both parts agree). Part 2 is the case the paper sets aside
"without loss of generality": a facility farther than the penalty is never used, so only its
multiplier changes the value. `|S| + 1 ≤ R` is the cardinality constraint (6c) of (MSF_i) for
`S ∪ {v}`, under which the closed form of `Φ_i` applies to both sets. `0 ≤ λ_i`,
`0 ≤ q_j < 1`, `R ≥ 1` are the standing assumptions of §3.1. -/
theorem marginal {J R : ℕ} (lam : ℝ) (d : Fin J → ℝ) (phi : ℝ) (q : Fin J → ℝ)
    (mu : Fin J → ℝ) (hlam : 0 ≤ lam) (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∀ j, q j < 1) (hR : 1 ≤ R)
    (S : Finset (Fin J)) (v : Fin J) (hv : v ∉ S) (hS : S.card + 1 ≤ R) (L : List (Fin J))
    (hLnd : L.Nodup) (hLS : L.toFinset = S) (hLsort : L.Pairwise (fun a b => d a ≤ d b)) :
    (d v ≤ phi →
      Phi lam d phi q mu R (insert v S) - Phi lam d phi q mu R S =
        lam * (1 - q v) * (prodQ q L (countLE d (d v) L) * d v -
          ∑ k ∈ Icc (countLE d (d v) L + 1) (countLE d phi L + 1), Ck d phi q L k) + mu v) ∧
    (phi ≤ d v →
      Phi lam d phi q mu R (insert v S) - Phi lam d phi q mu R S = mu v) := by sorry

end ReliableFacilityLoc.Supermod
