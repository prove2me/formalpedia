-- Prove2me | Theorems.Thm_QCollLB_lemma_5_22
-- name    : QCollLB.lemma_5_22
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:19:22.07121+00:00
-- url     : https://prove2.me/theorems/20133bbf-d794-4822-b0ae-017381b2a62d
-- title:
--   Lemma 5.22 — verification and recorded targets
-- statement:
--   Let $1\le k\le n$ and let $\mathcal B$ be a family of $k$-element subsets of $[n]$. Let $\eta_0\in D_{\le t}\otimes A$ with $\|\eta_0\|\le1$ store a proposed ordered $k$-tuple, and let $\eta_k$ be the state after the $k$ verification checks (repeated positions are rejecting branches and are kept; on valid branches each proposed position is queried into a fresh answer register by an unprojected auxiliary value query; dummy queries on rejecting branches; no renormalization). If $t+k<n$, then
--   $$
--   \|(I_D\otimes P_{\mathrm{ver}})\eta_k\|\le\|(P_{\mathrm{full}}\otimes I_A)\eta_k\|+k\sqrt{\frac2{n-t-k}} .
--   $$
--
--   An accepted output is thus, up to a small error, already a recorded target in the database.
--
--   Differences from the source:
--   - reading: "k fresh answer registers" → answer registers initialized to |0⟩ (freshAns); reason: the usual meaning of a fresh register; the consistency argument of the proof needs the register to start at 0
--   - reading: "use dummy queries on rejecting branches" → the identity on rejecting branches; reason: the paper fixes no particular dummy; rejecting branches are orthogonal in the tuple register and are annihilated by P_ver
--   - encoding: "invalid or repeated positions" → repeated positions (positions are Fin n); reason: every element of Fin n is a valid position
--   - encoding: A stores the proposed positions and the returned slots y_1, …, y_k → A = ℂ[[n]^k] ⊗ ℂ[W] (proposed ordered tuple and the rest of the workspace, W any finite type) with the k answer registers Z_{n+1}^k adjoined beside it; reason: the returned slots are the k fresh answer registers the checks write into; W arbitrary covers every workspace
--   - encoding: valid slots 1, …, n and blank 0 in Z_{n+1} → 0-based slot u in Fin n stored as u + 1 in ZMod (n+1), blank 0; reason: index shift; same instances
-- source:
--   Peng–Wu, Quantum Lower Bounds for Collision Problems, arXiv:2611.01767 (PDF sha256 4e5aba34…d9fc), Lemma 5.22, Eq. (62), p.42 (process p.42, Definition 5.21 p.41)

import Mathlib
import Definitions.Def_QCollLB_Harmonic
import Definitions.Def_QCollLB_Verification

namespace QCollLB

open CompPermOracle

/-- **Lemma 5.22 (Verification and recorded targets)** (Peng–Wu, arXiv:2611.01767 (PDF sha256
4e5aba34…d9fc), Lemma 5.22, Eq. (62), p.42, with the verification process of the paragraph before
it and Definition 5.21, p.41). Let `1 ≤ k ≤ n` and let `𝓑` be a family of `k`-element target sets.
Let `η_0 ∈ D_{≤t} ⊗ A` with `‖η_0‖ ≤ 1` store a proposed ordered `k`-tuple, and let `η_k` be the state
after the `k` checks (repeated positions flagged as rejecting branches and kept; on valid branches
the proposed positions are queried into `k` fresh answer registers by unprojected auxiliary value
queries; dummy queries on rejecting branches; no renormalization). If `t + k < n`, then
`‖(I_D ⊗ P_ver) η_k‖ ≤ ‖(P_full ⊗ I_A) η_k‖ + k √(2/(n − t − k))`.

**Formalization Note.** `A = ℂ[[n]^k] ⊗ ℂ[W]` (proposed tuple and the rest of the workspace, `W` an
arbitrary finite type); the fresh answer registers start at `|0⟩` (`freshAns`); `η_k` is
`verifyOp W (freshAns W ζ)` with the checks of `checkStep`; the dummy query is the identity.
`P_ver` and `P_full` are `Pver` and `PfullVer`. -/
theorem lemma_5_22 (n k t : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) (htk : t + k < n)
    (𝓑 : Finset (Finset (Fin n))) (h𝓑 : ∀ B ∈ 𝓑, B.card = k)
    (W : Type) [Fintype W] [DecidableEq W]
    (ζ : Hil (((Fin k → Fin n) × W) × PartialPerm n))
    (hζ : ζ ∈ ampSub (Λ := (Fin k → Fin n) × W) (DLe n t)) (hζ1 : ‖ζ‖ ≤ 1) :
    ‖Pver W 𝓑 (verifyOp W (freshAns W ζ))‖ ≤
      ‖PfullVer W 𝓑 (verifyOp W (freshAns W ζ))‖ +
        k * Real.sqrt (2 / ((n : ℝ) - t - k)) := by sorry

end QCollLB
