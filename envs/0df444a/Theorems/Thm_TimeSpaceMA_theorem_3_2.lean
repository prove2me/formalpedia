-- Prove2me | Theorems.Thm_TimeSpaceMA_theorem_3_2
-- name    : TimeSpaceMA.theorem_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:00:18.493206+00:00
-- url     : https://prove2.me/theorems/06594864-afb1-470e-9038-b2f3221650cf
-- title:
--   Theorem 3.2 — the trace theorem
-- statement:
--   Let $u=(u_p)_{p\in[q]^m}$ and $U=G^{\otimes m}u$, and call (1) the statement that some integer $v$ satisfies $\sum_{p\in[q]^m}\Phi(y_p,y_p)=0$ for $y_p=(v_p,u_p)$.
--
--   1. If (1) has an integer solution $v$, then the honest tables constructed from $v$ pass every round with probability $1$.
--   2. If (1) has no integer solution, then for every choice of the tables $W,R_1,\dots,R_{m-1}$, a round rejects with probability at least
--   $$\lambda:=\frac{\delta^{2m}}{4qL^2\kappa},\qquad\kappa:=\kappa_{2m}=4(4m)^8\delta^{-14m}.$$
--
--   This is the soundness core of the protocol: a table of any shape is caught by a few random queries.
--
--   Differences from the source:
--   - generalization: G the code of Lemma 3.10, Φ of Lemma 3.8(c), labels u = (1, c, c′) → any systematic subset-sum code with q ≥ 2 and the distance of Lemma 3.10(b); any integer bilinear form on ℤ^d ⊕ ℤ^e; any integer labels; reason: the proof on pp.15–16 uses only these properties, and the page's objects are instances
--   - encoding: "and 1/λ = K^{o(1)} by Fact 3.11" → not stated in this item; reason: it is a remark on parameter sizes which holds only for the protocol's q and m, and is absorbed by the goal theorem
--   - encoding: tables R_j for 1 ≤ j ≤ m−1 → a family R n indexed by n = m − j, with entries outside the range never read; reason: this avoids dependent casts and leaves the quantification over every choice of tables intact
-- source:
--   Williams, Xi, Short Non-Interactive Proofs for Time-Space Computations, STOC 2027 submission (manuscript sha256 184c2f95…), Theorem 3.2, p.15; Definition 3.18, p.14; (1), p.11

import Definitions.Def_TimeSpaceMA_RoundAccepts

namespace TimeSpaceMA

/-- **Theorem 3.2** (Trace theorem; Williams, Xi, STOC 2027 submission, manuscript sha256 184c2f95…, p.15).
Let `U = G^{⊗m} u`. (a) If (1) has an integer solution `v`, the honest tables from `v` pass every round. (b)
If (1) has no integer solution, then for every choice of the tables `W, R₁, …, R_{m−1}` a round rejects with
probability at least `λ := δ^{2m} / (4 q L² κ)`, `κ := κ_{2m} = 4 (4m)^8 δ^{−14m}`.

**Formalization Note** (1) reads `∃ v : [q]^m → ℤ^d, Σ_p Φ((v_p, u_p), (v_p, u_p)) = 0`. `G` is any
systematic subset-sum code with the distance of Lemma 3.10(b), `Φ` any integer bilinear form on
`ℤ^d ⊕ ℤ^e`, `u` any labels. `m ≥ 2` and `q ≥ 2` as on p.12. The remark "`1/λ = K^{o(1)}`" belongs to the
parameters and is not stated. -/
theorem theorem_3_2 {q L m d e : ℕ} (hq : 2 ≤ q) (hm : 2 ≤ m) (G : SubsetSumCode q L)
    (σ : Fin q → Fin L) (hσ : G.IsSystematic σ) (hG : G.HasGroupDistance)
    (Φ : (Fin d ⊕ Fin e → ℤ) →ₗ[ℤ] (Fin d ⊕ Fin e → ℤ) →ₗ[ℤ] ℤ)
    (u : (Fin m → Fin q) → Fin e → ℤ) :
    (∀ v : (Fin m → Fin q) → Fin d → ℤ,
      ∑ p, Φ (Sum.elim (v p) (u p)) (Sum.elim (v p) (u p)) = 0 →
      ∀ a b : Fin m → Fin L,
        RoundAccepts G σ Φ (tensorEncode G u) (tensorEncode G v)
          (fun n α β =>
            if hn : n ≤ m then
              honestTable σ (fun γ => Sum.elim (tensorEncode G v γ) (tensorEncode G u γ)) Φ n hn α β
            else 0)
          a b) ∧
    ((¬ ∃ v : (Fin m → Fin q) → Fin d → ℤ,
        ∑ p, Φ (Sum.elim (v p) (u p)) (Sum.elim (v p) (u p)) = 0) →
      ∀ (W : (Fin m → Fin L) → Fin d → ℤ)
        (R : (n : ℕ) → (Fin n → Fin L) → (Fin n → Fin L) → ℤ),
        G.delta ^ (2 * m) / (4 * (q : ℝ) * (L : ℝ) ^ 2 * kappa G.delta (2 * m)) ≤
          traceReject G σ Φ (tensorEncode G u) W R) := by sorry

end TimeSpaceMA
