-- Prove2me | Theorems.Thm_ReliableFacilityLoc_Supermod_bracket_nonpos
-- name    : ReliableFacilityLoc.Supermod.bracket_nonpos
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:14:53.59968+00:00
-- url     : https://prove2.me/theorems/d7484efc-e80e-4c1e-a719-62487a289185
-- title:
--   A.3: the bracket $P_t d_{iv} - \sum_{k=t+1}^{\bar n+1} C_k$ is nonpositive
-- statement:
--   Assume $0 \le q_j < 1$ for every regular facility. Let $j_1, \dots, j_n$ be regular facilities listed in nondecreasing order of distance $d_{ij}$, and let $v$ be a regular facility with $d_{iv} \le \varphi_i$. Let $\bar n$ and $t$ be the numbers of listed facilities with $d_{ij} \le \varphi_i$, resp. $d_{ij} \le d_{iv}$, and $P_k$, $C_k$ as in the proof of Proposition 3. Then
--
--   $$
--   P_t\, d_{iv} - \sum_{k=t+1}^{\bar n+1} C_k \le 0.
--   $$
--
--   Consequently, by the marginal-cost formula, adding a facility within the penalty distance changes the transportation part of $\Phi_i$ by a nonpositive amount, and this sign is what both cases of the proof of Proposition 3 rely on.
--
--   **Formalization Note** The paper claims the bracket is strictly negative; this fails when some $q_{j_k} = 0$ or when $d_{iv} = \varphi_i$ (for instance with an empty list and $d_{iv} = \varphi_i$ the bracket is $0$). Only the weak inequality is used in the proof, and it is what is stated. No sign is assumed on the distances.
-- source:
--   Cui, Ouyang, Shen, Reliable Facility Location Design under the Risk of Disruptions, UCTC-FR-2010-02 (Feb. 2010), p. 36 (PDF 38), Appendix A.3, "Note that the first item in the last equation is negative"

import Mathlib
import Definitions.Def_ReliableFacilityLoc_Supermod_RSP
import Definitions.Def_ReliableFacilityLoc_Supermod_ClosedForm

open Finset

namespace ReliableFacilityLoc.Supermod

/-- **Sign of the bracket in the marginal cost** (Cui, Ouyang & Shen, UCTC-FR-2010-02 (Feb. 2010),
Appendix A.3, p. 36, PDF 38). Let `L = [j_1, …, j_n]` be a list of regular facilities in
nondecreasing order of distance, and `v` a regular facility with `d_iv ≤ φ_i`; let `n̄`, `t` be the
numbers of entries with `d_ij ≤ φ_i`, resp. `d_ij ≤ d_iv`. Then
`P_t d_iv − Σ_{k=t+1}^{n̄+1} C_k ≤ 0`.

Printed (p. 36): "Note that the first item in the last equation is negative, because
Ptdiv − Σ_{k=t+1}^{n̄+1} Ck = Pt[div − Σ_{k=t+1}^{n̄} (Π_{ℓ=t+1}^{k−1} qjℓ)(1 − qjk)dijk −
(Π_{ℓ=t+1}^{n̄} qjℓ)φi] < Ptdiv[1 − (Π_{ℓ=t+1}^{k−1} qjℓ)(1 − qjk) − Π_{ℓ=t+1}^{n̄} qjℓ] = 0."

Formalization Note: the paper claims a strict inequality ("negative", "<"). It fails when some
`q_{j_k} = 0` cuts the chain or when `d_iv = φ_i` (e.g. `L = []`, `d_iv = φ_i` gives `0`); only
"`≤ 0`" is used in the proof, so "`≤ 0`" is stated. The printed second line also omits the sum
over `k`. The list need not be the list of a set avoiding `v`, and no cardinality bound is needed:
the claim is an inequality about the numbers `P_k`, `C_k` alone. `0 ≤ q_j < 1` is the standing
assumption of §3.1 (`q_j ≤ 1` suffices). -/
theorem bracket_nonpos {J : ℕ} (d : Fin J → ℝ) (phi : ℝ) (q : Fin J → ℝ)
    (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∀ j, q j < 1) (L : List (Fin J))
    (hLsort : L.Pairwise (fun a b => d a ≤ d b)) (v : Fin J) (hv : d v ≤ phi) :
    prodQ q L (countLE d (d v) L) * d v -
      ∑ k ∈ Icc (countLE d (d v) L + 1) (countLE d phi L + 1), Ck d phi q L k ≤ 0 := by sorry

end ReliableFacilityLoc.Supermod
