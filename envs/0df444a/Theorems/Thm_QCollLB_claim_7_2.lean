-- Prove2me | Theorems.Thm_QCollLB_claim_7_2
-- name    : QCollLB.claim_7_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:18:16.613194+00:00
-- url     : https://prove2.me/theorems/e68ceb11-f257-4d7f-a62f-80599e42b3f1
-- title:
--   Claim 7.2 — iterated harmonic difference bound
-- statement:
--   Let $1\le k\le s<n/2$, let $u_1,\dots,u_k\in[n]$ be distinct, $B=\{u_1,\dots,u_k\}$ and $T_j=\{u_j,\dots,u_k\}$. For every range-harmonic $w\in D^{(s)}_R$,
--   $$
--   \|P_Bw\|^2\le\frac1{(n-s+1)^k}\sum_{\substack{v_j\in[n]\setminus T_j\\1\le j\le k}}\big\|(I_D-L_{(u_kv_k)})\cdots(I_D-L_{(u_1v_1)})\,w\big\|^2,
--   $$
--   where $L_\tau$ is range relabelling and $(u\,v)$ a transposition.
--
--   It converts the weight of databases containing all of $B$ into mixed differences of $w$ under value swaps.
--
--   Differences from the source:
--   - encoding: indices 1..k and s < n/2 → 0-based tuples u, v : Fin k → Fin n and 2s < n; reason: same instances
-- source:
--   Peng–Wu, Quantum Lower Bounds for Collision Problems, arXiv:2611.01767 (PDF sha256 4e5aba34…d9fc), Claim 7.2, p.52

import Mathlib
import Definitions.Def_QCollLB_Harmonic

namespace QCollLB

open CompPermOracle

/-- **Claim 7.2 (Iterated harmonic difference bound)** (Peng–Wu, arXiv:2611.01767 (PDF sha256
4e5aba34…d9fc), Claim 7.2, p.52). Let `1 ≤ k ≤ s < n/2`, fix distinct values `u_1, …, u_k`, and put
`B = {u_1, …, u_k}`, `T_j = {u_j, …, u_k}`. For `w ∈ D^{(s)}_R`,
`‖P_B w‖² ≤ (n − s + 1)^{−k} Σ_{v_j ∈ [n] ∖ T_j, 1 ≤ j ≤ k}
‖(I_D − L_{(u_k v_k)}) ⋯ (I_D − L_{(u_1 v_1)}) w‖²`.

**Formalization Note.** Indices are 0-based (`u, v : Fin k → Fin n`); `L_τ|d⟩ = |τ ∘ d⟩` is
`rangeOp n τ` and `(u v)` is `Equiv.swap u v`. `s < n/2` is written `2s < n`. The sum ranges over all
tuples `v` with `v_j ∉ T_j` for every `j`. -/
theorem claim_7_2 (n k s : ℕ) (hk : 1 ≤ k) (hks : k ≤ s) (hsn : 2 * s < n)
    (u : Fin k → Fin n) (hu : Function.Injective u) (w : Hil (PartialPerm n))
    (hw : w ∈ DRs n s) :
    ‖PB (Finset.univ.image u) w‖ ^ 2 ≤
      1 / ((n : ℝ) - s + 1) ^ k *
        ∑ v ∈ Finset.univ.filter (fun v : Fin k → Fin n => ∀ j, v j ∉ Tset u j),
          ‖iterDiff (rangeOp n) u v w‖ ^ 2 := by sorry

end QCollLB
