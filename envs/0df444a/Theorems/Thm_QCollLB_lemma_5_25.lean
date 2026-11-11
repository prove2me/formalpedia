-- Prove2me | Theorems.Thm_QCollLB_lemma_5_25
-- name    : QCollLB.lemma_5_25
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:19:31.19625+00:00
-- url     : https://prove2.me/theorems/20d3187a-0386-4cdc-9781-44cea64f983d
-- title:
--   Lemma 5.25 — success bound for Permutation Bucket Finding
-- statement:
--   For each $k\ge2$ there is $C_k$, depending only on $k$, such that the following holds for public buckets of size $k$. If $\psi\in P_{\le t}\otimes A$ is a unit state storing a proposed ordered $k$-tuple and $t+k+3\le n/8$, then
--   $$
--   \sqrt{p_{\mathrm{succ}}}\le\|(P_{\mathrm{full}}\otimes I_A)(V\otimes I_A)\psi\|+C_k\sqrt{\frac{t+k+1}n},
--   $$
--   where $p_{\mathrm{succ}}$ is the probability that the tuple is a valid output for Permutation Bucket Finding.
--
--   Success therefore requires the encoded database to contain a full bucket already before any checks.
--
--   Differences from the source:
--   - encoding: A stores a proposed ordered k-tuple → A = ℂ[[n]^k] ⊗ ℂ[W] with W an arbitrary finite type, written first; reason: an arbitrary workspace next to the tuple register
--   - encoding: p_succ, the probability that the tuple is a valid output → ‖Π_succ ψ‖² with Π_succ the diagonal projector of the success event; reason: the probability of an event in a joint state
--   - encoding: n = kN with a fixed public partition → any n and any bucket map b : Fin n → Fin N with fibres of size k; reason: such a map forces n = kN
-- source:
--   Peng–Wu, Quantum Lower Bounds for Collision Problems, arXiv:2611.01767 (PDF sha256 4e5aba34…d9fc), Lemma 5.25, Eq. (65), p.45

import Mathlib
import Definitions.Def_QCollLB_Buckets
import Definitions.Def_QCollLB_Harmonic
import Definitions.Def_QCollLB_Verification

namespace QCollLB

open CompPermOracle

/-- **Lemma 5.25 (Success bound for Permutation Bucket Finding)** (Peng–Wu, arXiv:2611.01767 (PDF
sha256 4e5aba34…d9fc), Lemma 5.25, Eq. (65), p.45). For each `k ≥ 2` there is `C_k`, depending only on
`k`, such that for public buckets of size `k`: if `ψ ∈ P_{≤t} ⊗ A` is a unit state with a proposed
ordered `k`-tuple stored in `A` and `t + k + 3 ≤ n/8`, then
`√p_succ ≤ ‖(P_full ⊗ I_A)(V ⊗ I_A) ψ‖ + C_k √((t + k + 1)/n)`, where `p_succ` is the probability that
the tuple is a valid output for Permutation Bucket Finding (p.45).

**Formalization Note.** `A = ℂ[[n]^k] ⊗ ℂ[W]` (the tuple and the rest of the workspace, `W` any
finite type), written first. `P_full` is for the bucket family `{B_1, …, B_N}` (`= P_{k,≥1}`, p.43).
`p_succ = ‖Π_succ ψ‖²` with `Π_succ` the diagonal projector onto "the tuple's entries are distinct and
`π(tuple) = B_y` for some `y`" (`psucc`). `C_k` is chosen before `n, N, b, t, W, ψ`. -/
theorem lemma_5_25 (k : ℕ) (hk : 2 ≤ k) :
    ∃ C : ℝ, ∀ (n N : ℕ) (b : Fin n → Fin N), IsBucketMap k b →
      ∀ t : ℕ, ((t : ℝ) + k + 3 ≤ (n : ℝ) / 8) →
      ∀ (W : Type) [Fintype W] [DecidableEq W]
        (ψ : Hil (((Fin k → Fin n) × W) × Equiv.Perm (Fin n))),
        ψ ∈ ampSub (Λ := (Fin k → Fin n) × W) (PLe n t) → ‖ψ‖ = 1 →
        Real.sqrt (psucc W b ψ) ≤
          ‖opTensor (1 : Hil ((Fin k → Fin n) × W) →L[ℂ] Hil ((Fin k → Fin n) × W))
              (Pfull (bucketFamily b))
              (opTensor (1 : Hil ((Fin k → Fin n) × W) →L[ℂ] Hil ((Fin k → Fin n) × W)) (V n) ψ)‖ +
            C * Real.sqrt (((t : ℝ) + k + 1) / n) := by sorry

end QCollLB
