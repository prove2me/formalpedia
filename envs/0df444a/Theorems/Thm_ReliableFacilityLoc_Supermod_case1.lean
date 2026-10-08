-- Prove2me | Theorems.Thm_ReliableFacilityLoc_Supermod_case1
-- name    : ReliableFacilityLoc.Supermod.case1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:16:08.694976+00:00
-- url     : https://prove2.me/theorems/82d8e726-515a-49d4-bf64-499d06ca67be
-- title:
--   A.3, Case 1 ($d_{iu} \le d_{iv}$): $\Phi_i(S\cup\{u,v\}) - \Phi_i(S\cup\{u\})$
-- statement:
--   Assume $\lambda_i \ge 0$, $0 \le q_j < 1$ and $R \ge 1$. Let $S$ be a set of regular facilities, $u \ne v$ regular facilities not in $S$ with $|S| + 2 \le R$ and $d_{iu} \le d_{iv} \le \varphi_i$. List $S$ in nondecreasing order of distance and let $\bar n$, $t$, $P_k$, $C_k$ be computed from $S$, with $t$ the number of facilities of $S$ with $d_{ij} \le d_{iv}$. Then
--
--   $$
--   \Phi_i(S\cup\{u,v\}) - \Phi_i(S\cup\{u\}) = \lambda_i\, q_u (1-q_v)\Big(P_t\, d_{iv} - \sum_{k=t+1}^{\bar n+1} C_k\Big) + \mu_{iv}.
--   $$
--
--   Compared with the marginal cost of $v$ at $S$, the transportation part is multiplied by $q_u \in [0,1]$, because $u$ is now served before $v$. Together with the sign of the bracket, this gives inequality (18) in this case.
--
--   **Formalization Note** The printed computation has two typos, $(1-q_t)$ for $(1-q_v)$ and $u_{iv}$ for $\mu_{iv}$; the final line, which is stated, is correct. The bound $d_{iv} \le \varphi_i$ is the paper's "without loss of generality" assumption.
-- source:
--   Cui, Ouyang, Shen, Reliable Facility Location Design under the Risk of Disruptions, UCTC-FR-2010-02 (Feb. 2010), p. 36 (PDF 38), Appendix A.3, Case 1

import Mathlib
import Definitions.Def_ReliableFacilityLoc_Supermod_RSP
import Definitions.Def_ReliableFacilityLoc_Supermod_ClosedForm

open Finset

namespace ReliableFacilityLoc.Supermod

/-- **Case 1 of the proof of Proposition 3, `d_iu ≤ d_iv`** (Cui, Ouyang & Shen, UCTC-FR-2010-02
(Feb. 2010), Appendix A.3, p. 36, PDF 38). Let `S` be a set of regular facilities, `u ≠ v` regular
facilities not in `S` with `|S| + 2 ≤ R` and `d_iu ≤ d_iv ≤ φ_i`, and `L = [j_1, …, j_n]` a list
of `S` in nondecreasing order of distance; `n̄`, `t`, `P_k`, `C_k` are computed from `S`. Then
`Φ_i(S ∪ {u, v}) − Φ_i(S ∪ {u}) = λ_i q_u (1 − q_v)(P_t d_iv − Σ_{k=t+1}^{n̄+1} C_k) + µ_iv`.

Printed (p. 36): "Case 1: diu ≤ div. In this case, it follows that Φi(S ∪ {u, v}) − Φi(S ∪ {u}) =
… = λi[quPt(1 − qv)div − qu(1 − qv) Σ_{k=t+1}^{n̄+1} Ck] + uiv = λiqu(1 − qv)(Ptdiv −
Σ_{k=t+1}^{n̄+1} Ck) + µiv."

Formalization Note: the printed first line has "`q_u P_t (1 − q_t) d_iv`" for `q_u P_t (1 − q_v) d_iv`
and the second line "`u_iv`" for `µ_iv`; both are typos (the last line is as stated). `d_iv ≤ φ_i`
is the paper's "without loss of generality" assumption of p. 36. `|S| + 2 ≤ R` makes `S ∪ {u, v}`
satisfy (6c), so that the closed form applies to every set involved. `0 ≤ λ_i`, `0 ≤ q_j < 1`,
`R ≥ 1` are the standing assumptions of §3.1. -/
theorem case1 {J R : ℕ} (lam : ℝ) (d : Fin J → ℝ) (phi : ℝ) (q : Fin J → ℝ)
    (mu : Fin J → ℝ) (hlam : 0 ≤ lam) (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∀ j, q j < 1) (hR : 1 ≤ R)
    (S : Finset (Fin J)) (u v : Fin J) (huv : u ≠ v) (hu : u ∉ S) (hv : v ∉ S)
    (hS : S.card + 2 ≤ R) (L : List (Fin J)) (hLnd : L.Nodup) (hLS : L.toFinset = S)
    (hLsort : L.Pairwise (fun a b => d a ≤ d b)) (hduv : d u ≤ d v) (hdv : d v ≤ phi) :
    Phi lam d phi q mu R (insert u (insert v S)) - Phi lam d phi q mu R (insert u S) =
      lam * q u * (1 - q v) * (prodQ q L (countLE d (d v) L) * d v -
        ∑ k ∈ Icc (countLE d (d v) L + 1) (countLE d phi L + 1), Ck d phi q L k) + mu v := by sorry

end ReliableFacilityLoc.Supermod
