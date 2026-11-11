-- Prove2me | Theorems.Thm_QCollLB_lemma_5_24
-- name    : QCollLB.lemma_5_24
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:20:11.883294+00:00
-- url     : https://prove2.me/theorems/8a8b89ef-b162-40bf-98dd-4329ce9aabc1
-- title:
--   Lemma 5.24 — one-query bound for creating partial collisions
-- statement:
--   Fix public buckets of size $k$ and integers $T,j,\ell$ with $0\le T<n$, $2\le j\le k$, $\ell\ge1$, and let $R\ge0$. Then
--   $$
--   \big\|P_{j,\ge\ell}\,O\,P_{j,=\ell-1}P_{j-1,\le R}\big\|_{D_{\le T}\otimes A}\le2\sqrt{\frac{2kR}{n-T}},
--   $$
--   and for every integer $h\ge0$, $P_{j,\ge h+2}\,O\,P_{j,\le h}=0$. Here $O$ is the controlled auxiliary query and $P_{j,\cdot}$ are the projectors for the collision count $L_j$.
--
--   One auxiliary query increases $L_j$ by at most one, and does so with small amplitude when few $(j-1)$-collisions are recorded.
--
--   Differences from the source:
--   - encoding: O = ⊕_{i,c} O_{i,c} on D ⊗ I ⊗ C_π (⊗ W_π) → the controlled auxiliary query over an arbitrary finite control register Λ carrying the position i(ℓ) and label c(ℓ), written first; reason: Λ = [n] × Z_{n+1} × W_π recovers O ⊗ I_{W_π}; any other Λ is such a controlled sum
--   - encoding: operator norm on D_{≤T} ⊗ A → ‖X v‖ ≤ c‖v‖ for all v ∈ D_{≤T} ⊗ ℂ[Λ]; reason: equivalent definition
--   - encoding: a fixed public partition into buckets of size k with n = kN → any bucket map b from Fin n to Fin N whose fibres have size k; reason: a bucket map is exactly such a partition; it forces n = kN
--   - encoding: phase ω_{n+1}^{c·d(i)} with slots 1, …, n → stdPhase n c (0-based slot u gets ω_{n+1}^{c(u+1)}, blank gets 1); reason: index shift; same operator
-- source:
--   Peng–Wu, Quantum Lower Bounds for Collision Problems, arXiv:2611.01767 (PDF sha256 4e5aba34…d9fc), Lemma 5.24, Eqs. (63)–(64), p.43

import Mathlib
import Definitions.Def_QCollLB_Buckets
import Definitions.Def_QCollLB_Harmonic
import Definitions.Def_QCollLB_Queries
import Definitions.Def_QCollLB_Verification

namespace QCollLB

open CompPermOracle

/-- **Lemma 5.24 (One-query bound for creating partial collisions)** (Peng–Wu, arXiv:2611.01767
(PDF sha256 4e5aba34…d9fc), Lemma 5.24, Eqs. (63)–(64), p.43). Fix public buckets of size `k`, and
integers `T, j, ℓ` with `0 ≤ T < n`, `2 ≤ j ≤ k`, `ℓ ≥ 1`, and let `R ≥ 0`. Then
`‖P_{j,≥ℓ} O P_{j,=ℓ−1} P_{j−1,≤R}‖_{D_{≤T} ⊗ A} ≤ 2 √(2kR/(n − T))` (63), and for every integer
`h ≥ 0`, `P_{j,≥h+2} O P_{j,≤h} = 0` (64).

**Formalization Note.** `O` is the controlled auxiliary query with the standard phases
`ω_{n+1}^{c·slot}` (Definition 5.3): a control register `Λ` (any finite type; `[n] × Z_{n+1} × W_π`
recovers `O ⊗ I_{W_π}`) carries the position `i(ℓ)` and the answer label `c(ℓ)`; it is written first.
The threshold projectors use `L_j = MultiCollQ.levelCount b j`. The norm on `D_{≤T} ⊗ A` is written as
`‖X v‖ ≤ c ‖v‖` for `v` in that subspace. `R` is real, as printed. -/
theorem lemma_5_24 {n N : ℕ} (k : ℕ) (b : Fin n → Fin N) (hb : IsBucketMap k b)
    (T j ℓ : ℕ) (hT : T < n) (hj : 2 ≤ j) (hjk : j ≤ k) (hℓ : 1 ≤ ℓ) (R : ℝ) (hR : 0 ≤ R)
    (Λ : Type) [Fintype Λ] [DecidableEq Λ] (i : Λ → Fin n) (c : Λ → ZMod (n + 1)) :
    (∀ v ∈ ampSub (Λ := Λ) (DLe n T),
      ‖opTensor (1 : Hil Λ →L[ℂ] Hil Λ) (threshProj b j (fun m => ℓ ≤ m))
          (auxCtl i (fun l => stdPhase n (c l))
            (opTensor (1 : Hil Λ →L[ℂ] Hil Λ)
              ((threshProj b j (fun m => m = ℓ - 1)).comp
                (threshProj b (j - 1) (fun m => (m : ℝ) ≤ R))) v))‖ ≤
        2 * Real.sqrt (2 * k * R / ((n : ℝ) - T)) * ‖v‖) ∧
    ∀ h : ℕ,
      (opTensor (1 : Hil Λ →L[ℂ] Hil Λ) (threshProj b j (fun m => h + 2 ≤ m))).comp
          ((auxCtl i (fun l => stdPhase n (c l))).comp
            (opTensor (1 : Hil Λ →L[ℂ] Hil Λ) (threshProj b j (fun m => m ≤ h)))) = 0 := by sorry

end QCollLB
