-- Prove2me | Theorems.Thm_ReliableFacilityLoc_Supermod_case2
-- name    : ReliableFacilityLoc.Supermod.case2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:14:49.025975+00:00
-- url     : https://prove2.me/theorems/93ec67db-0af9-45d6-a235-077eaa1a871b
-- title:
--   A.3, Case 2 ($d_{iu} > d_{iv}$): $\Phi_i(S\cup\{u,v\}) - \Phi_i(S\cup\{u\})$
-- statement:
--   Assume $\lambda_i \ge 0$, $0 \le q_j < 1$ and $R \ge 1$. Let $S$ be a set of regular facilities, $u \ne v$ regular facilities not in $S$ with $|S| + 2 \le R$ and $d_{iv} < d_{iu} \le \varphi_i$. List $S$ in nondecreasing order of distance and let $\bar n$, $s$, $t$, $P_k$, $C_k$ be computed from $S$, where $s$ and $t$ are the numbers of facilities of $S$ with $d_{ij} \le d_{iu}$, resp. $d_{ij} \le d_{iv}$ (so $t \le s$). Then
--
--   $$
--   \Phi_i(S\cup\{u,v\}) - \Phi_i(S\cup\{u\}) = \lambda_i (1-q_v)\Big\{P_t\, d_{iv} - \Big[\sum_{k=t+1}^{s} C_k + P_s(1-q_u)\,d_{iu} + q_u \sum_{k=s+1}^{\bar n+1} C_k\Big]\Big\} + \mu_{iv}.
--   $$
--
--   The bracket is the expected cost, in $S \cup \{u\}$, of the levels after the $t$-th; comparing it with $\sum_{k=t+1}^{\bar n+1} C_k$ yields inequality (18) in this case.
--
--   **Formalization Note** The bound $d_{iu} \le \varphi_i$ is the paper's "without loss of generality" assumption. The paper's justification of (18) in this case passes through an intermediate "$\le$" line that does not hold as printed; the difference of the two brackets is in fact equal to $(1-q_u)\big[P_s d_{iu} - \sum_{k=s+1}^{\bar n+1} C_k\big]$. That justification is not part of this statement.
-- source:
--   Cui, Ouyang, Shen, Reliable Facility Location Design under the Risk of Disruptions, UCTC-FR-2010-02 (Feb. 2010), p. 37 (PDF 39), Appendix A.3, Case 2

import Mathlib
import Definitions.Def_ReliableFacilityLoc_Supermod_RSP
import Definitions.Def_ReliableFacilityLoc_Supermod_ClosedForm

open Finset

namespace ReliableFacilityLoc.Supermod

/-- **Case 2 of the proof of Proposition 3, `d_iu > d_iv`** (Cui, Ouyang & Shen, UCTC-FR-2010-02
(Feb. 2010), Appendix A.3, p. 37, PDF 39). Let `S` be a set of regular facilities, `u ≠ v` regular
facilities not in `S` with `|S| + 2 ≤ R` and `d_iv < d_iu ≤ φ_i`, and `L = [j_1, …, j_n]` a list
of `S` in nondecreasing order of distance; `n̄`, `s`, `t`, `P_k`, `C_k` are computed from `S`
(`s`, `t` the numbers of elements with `d_ij ≤ d_iu`, resp. `d_ij ≤ d_iv`). Then
`Φ_i(S ∪ {u, v}) − Φ_i(S ∪ {u}) = λ_i (1 − q_v){P_t d_iv − [Σ_{k=t+1}^{s} C_k + P_s(1 − q_u) d_iu
+ q_u Σ_{k=s+1}^{n̄+1} C_k]} + µ_iv`.

Printed (p. 37): "Case 2: diu > div. In this case t ≤ s, and the following assertion holds:
Φi(S ∪ {u, v}) − Φi(S ∪ {u}) = … = λi(1 − qv){Ptdiv − [Σ_{k=t+1}^{s} Ck + Ps(1 − qu)diu +
qu Σ_{k=s+1}^{n̄+1} Ck]} + µiv."

Formalization Note: `d_iu ≤ φ_i` is the paper's "without loss of generality" assumption of p. 36.
`|S| + 2 ≤ R` makes `S ∪ {u, v}` satisfy (6c), so that the closed form applies to every set
involved. `0 ≤ λ_i`, `0 ≤ q_j < 1`, `R ≥ 1` are the standing assumptions of §3.1. -/
theorem case2 {J R : ℕ} (lam : ℝ) (d : Fin J → ℝ) (phi : ℝ) (q : Fin J → ℝ)
    (mu : Fin J → ℝ) (hlam : 0 ≤ lam) (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∀ j, q j < 1) (hR : 1 ≤ R)
    (S : Finset (Fin J)) (u v : Fin J) (huv : u ≠ v) (hu : u ∉ S) (hv : v ∉ S)
    (hS : S.card + 2 ≤ R) (L : List (Fin J)) (hLnd : L.Nodup) (hLS : L.toFinset = S)
    (hLsort : L.Pairwise (fun a b => d a ≤ d b)) (hdvu : d v < d u) (hdu : d u ≤ phi) :
    Phi lam d phi q mu R (insert u (insert v S)) - Phi lam d phi q mu R (insert u S) =
      lam * (1 - q v) * (prodQ q L (countLE d (d v) L) * d v -
        (∑ k ∈ Icc (countLE d (d v) L + 1) (countLE d (d u) L), Ck d phi q L k +
          prodQ q L (countLE d (d u) L) * (1 - q u) * d u +
          q u * ∑ k ∈ Icc (countLE d (d u) L + 1) (countLE d phi L + 1), Ck d phi q L k)) +
        mu v := by sorry

end ReliableFacilityLoc.Supermod
