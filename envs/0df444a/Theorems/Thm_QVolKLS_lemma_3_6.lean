-- Prove2me | Theorems.Thm_QVolKLS_lemma_3_6
-- name    : QVolKLS.lemma_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:38:33.574196+00:00
-- url     : https://prove2.me/theorems/c55cf3a4-38c4-4879-adf3-17a5d5fe5c1b
-- title:
--   Lemma 3.6 — composition of approximate quantum channels: $d_{\mathrm{tr}}(\tilde\rho_T,\rho_T)\le e_{\mathrm{init}}+\sum_k(\varepsilon_k+\Delta_k)$
-- statement:
--   Let $T\ge1$, let $\mathcal E_0,\dots,\mathcal E_{T-1}$ (primitives) and $\tilde{\mathcal E}_0,\dots,\tilde{\mathcal E}_{T-1}$ (their implementations) be completely positive trace-preserving maps, and let $\rho_0,\dots,\rho_T$ be reference density operators on all registers just before the corresponding channels. Suppose that for each $k$
--   $$
--   d_{\mathrm{tr}}\big(\mathcal E_k(\rho_k),\rho_{k+1}\big)\le\varepsilon_k,\qquad d_{\mathrm{tr}}\big(\tilde{\mathcal E}_k(\rho_k),\mathcal E_k(\rho_k)\big)\le\Delta_k .\tag{20–21}
--   $$
--   If the actual states evolve as $\tilde\rho_{k+1}=\tilde{\mathcal E}_k(\tilde\rho_k)$ and $d_{\mathrm{tr}}(\tilde\rho_0,\rho_0)\le e_{\mathrm{init}}$, then
--   $$
--   d_{\mathrm{tr}}(\tilde\rho_T,\rho_T)\le e_{\mathrm{init}}+\sum_{k=0}^{T-1}(\varepsilon_k+\Delta_k).\tag{22}
--   $$
--
--   This is the error ledger of the whole volume algorithm.
--
--   **Formalization Note** CPTP maps are the published `QAlgorithms.IsChannel` (finite normalized Kraus families); register dimensions may change from step to step.
--
--   Differences from the source:
--   - encoding: completely positive trace-preserving maps → QAlgorithms.IsChannel (a finite normalized Kraus family); reason: equivalent in finite dimension
--   - encoding: density operators on all registers → positive semidefinite matrices of trace 1 on ℂ^{n_k}, n_k the dimension before step k; reason: registers are finite (p.21)
-- source:
--   R. Zhang, Improved Upper and Lower Bounds for Quantum Convex-Body Volume Estimation, arXiv:2610.04987 (preprint, held version, sha256 eee7a45e7117af08035a8d75fd6f145fa82ddade51ad87a6507911b6a0aa4f80), Lemma 3.6, p.29

import Definitions.Def_QVolKLS_fourthMomentNorm
import Definitions.Def_QAlgorithms_Defs_Channel

set_option autoImplicit false

namespace QVolKLS

open QAlgorithms
open scoped ComplexOrder

/-- R. Zhang, arXiv:2610.04987 (held version, sha256 eee7a45e…), **Lemma 3.6 (Composition of
approximate quantum channels)**, p.29. For `T ≥ 1` let `E_0, …, E_{T−1}` (primitives) and
`Ẽ_0, …, Ẽ_{T−1}` (implementations) be completely positive trace-preserving maps, and `ρ_0, …, ρ_T`
reference density operators, with `d_tr(E_k(ρ_k), ρ_{k+1}) ≤ ε_k` (20) and
`d_tr(Ẽ_k(ρ_k), E_k(ρ_k)) ≤ ∆_k` (21). If the actual states evolve as `ρ̃_{k+1} = Ẽ_k(ρ̃_k)` and
`d_tr(ρ̃_0, ρ_0) ≤ e_init`, then `d_tr(ρ̃_T, ρ_T) ≤ e_init + Σ_{k=0}^{T−1}(ε_k + ∆_k)` (22).

**Formalization Note.** The registers before step `k` have dimension `n k` (channels may discard or
add registers). CPTP maps are the published `QAlgorithms.IsChannel` (a finite normalized Kraus family,
equivalent to CPTP in finite dimension). A density operator is positive semidefinite with trace `1`.
`d_tr = ½‖·‖₁` (`traceDist`). -/
theorem lemma_3_6 (T : ℕ) (hT : 1 ≤ T) (n : ℕ → ℕ)
    (E Et : (k : ℕ) → Superop (Fin (n k)) (Fin (n (k + 1))))
    (hE : ∀ k < T, IsChannel (E k)) (hEt : ∀ k < T, IsChannel (Et k))
    (ρ ρt : (k : ℕ) → Matrix (Fin (n k)) (Fin (n k)) ℂ)
    (hρ : ∀ k ≤ T, (ρ k).PosSemidef ∧ (ρ k).trace = 1)
    (hρt0 : (ρt 0).PosSemidef ∧ (ρt 0).trace = 1)
    (hevol : ∀ k < T, ρt (k + 1) = Et k (ρt k))
    (eps Δ : ℕ → ℝ) (einit : ℝ)
    (h20 : ∀ k < T, traceDist (E k (ρ k)) (ρ (k + 1)) ≤ eps k)
    (h21 : ∀ k < T, traceDist (Et k (ρ k)) (E k (ρ k)) ≤ Δ k)
    (hinit : traceDist (ρt 0) (ρ 0) ≤ einit) :
    traceDist (ρt T) (ρ T) ≤ einit + ∑ k ∈ Finset.range T, (eps k + Δ k) := by sorry

end QVolKLS
