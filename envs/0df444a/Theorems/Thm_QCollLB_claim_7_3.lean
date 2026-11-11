-- Prove2me | Theorems.Thm_QCollLB_claim_7_3
-- name    : QCollLB.claim_7_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:19:50.8372+00:00
-- url     : https://prove2.me/theorems/8ac81937-02e5-4508-994e-1c418389e541
-- title:
--   Claim 7.3 — forest bound for mixed differences
-- statement:
--   Let $k\ge1$. There is a constant $C_k$, depending only on $k$, such that for all integers $n\ge2k$ and $1\le t<n/2$, every $S\subseteq[n]$ with $|S|\le t$, every $h:S_n\to\mathbb C$ that depends only on $\pi|_S$ with $\|h\|_\infty\le1$, and all distinct $u_1,\dots,u_k\in[n]$, with $T_j=\{u_j,\dots,u_k\}$,
--   $$
--   \sum_{\substack{v_j\in[n]\setminus T_j\\1\le j\le k}}\big\|(I_P-L_{(u_kv_k)})\cdots(I_P-L_{(u_1v_1)})\,h\big\|^2\le C_k\,t^k,
--   $$
--   the norm taken with respect to the uniform measure on $S_n$ and $L_\tau h(\pi)=h(\tau^{-1}\circ\pi)$.
--
--   Differences from the source:
--   - encoding: h as a function with the uniform-measure norm → the vector n!^{−1/2} Σ_π h(π)|π⟩ ∈ P with its Euclidean norm, and L_τ the left-regular operator; reason: the two norms coincide and L_τ on the vector is (L_τ h)(π) = h(τ^{−1}π)
--   - encoding: indices 1..k and t < n/2 → 0-based tuples and 2t < n; reason: same instances
-- source:
--   Peng–Wu, Quantum Lower Bounds for Collision Problems, arXiv:2611.01767 (PDF sha256 4e5aba34…d9fc), Claim 7.3, p.53

import Mathlib
import Definitions.Def_QCollLB_Harmonic

namespace QCollLB

open CompPermOracle

/-- **Claim 7.3 (A forest bound for mixed differences)** (Peng–Wu, arXiv:2611.01767 (PDF sha256
4e5aba34…d9fc), Claim 7.3, p.53). Let `k ≥ 1`. There is `C_k`, depending only on `k`, such that for
all integers `n ≥ 2k` and `1 ≤ t < n/2`, every `S ⊆ [n]` with `|S| ≤ t`, every `h : S_n → ℂ` depending
only on `π|_S` with `‖h‖_∞ ≤ 1`, and all distinct `u_1, …, u_k ∈ [n]`, with `T_j = {u_j, …, u_k}`,
`Σ_{v_j ∈ [n] ∖ T_j, 1 ≤ j ≤ k} ‖(I_P − L_{(u_k v_k)}) ⋯ (I_P − L_{(u_1 v_1)}) h‖² ≤ C_k t^k`,
the norm taken with respect to the uniform measure on `S_n`.

**Formalization Note.** `h` is the vector `funVec h = n!^{−1/2} Σ_π h(π)|π⟩ ∈ P`, whose Euclidean
norm is the uniform-measure norm `((1/n!) Σ_π |h(π)|²)^{1/2}`; `L_τ` is the left-regular operator
`|π⟩ ↦ |τ ∘ π⟩` (`leftOp n τ`), i.e. `(L_τ h)(π) = h(τ^{−1} ∘ π)`, which for a transposition is
`h(τ ∘ π)`. Indices are 0-based; `t < n/2` is `2t < n`. `C_k` is chosen before `n, t, S, h, u`. -/
theorem claim_7_3 (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, ∀ (n t : ℕ), 2 * k ≤ n → 1 ≤ t → 2 * t < n →
      ∀ (S : Finset (Fin n)), S.card ≤ t →
      ∀ h : Equiv.Perm (Fin n) → ℂ,
        (∀ π π' : Equiv.Perm (Fin n), (∀ i ∈ S, π i = π' i) → h π = h π') →
        (∀ π, ‖h π‖ ≤ 1) →
      ∀ u : Fin k → Fin n, Function.Injective u →
        ∑ v ∈ Finset.univ.filter (fun v : Fin k → Fin n => ∀ j, v j ∉ Tset u j),
          ‖iterDiff (leftOp n) u v (funVec h)‖ ^ 2 ≤ C * (t : ℝ) ^ k := by sorry

end QCollLB
