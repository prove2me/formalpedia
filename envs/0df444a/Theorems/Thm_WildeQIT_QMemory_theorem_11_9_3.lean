-- Prove2me | Theorems.Thm_WildeQIT_QMemory_theorem_11_9_3
-- name    : WildeQIT.QMemory.theorem_11_9_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:58:06.112121+00:00
-- url     : https://prove2.me/theorems/46916ca2-72d9-4f49-984b-4a5cf264a622
-- title:
--   Theorem 11.9.3 — data processing for coherent information
-- statement:
--   Let $\rho_{AB}$ be a state on $\mathcal H_A\otimes\mathcal H_B$ and $\mathcal N:\mathcal L(\mathcal H_B)\to\mathcal L(\mathcal H_{B'})$ a quantum channel, and set $\sigma_{AB'}\equiv\mathcal N_{B\to B'}(\rho_{AB})$. Then
--
--   $$
--   I(A\rangle B)_\rho\ge I(A\rangle B')_\sigma .
--   $$
--
--   Processing Bob's system with a channel cannot increase the coherent information, the quantum analogue of the classical data-processing inequality.
--
--   **Formalization Note** The channel is the published `WildeQIT.QChannel` (Choi–Kraus form) acting as $\mathrm{id}_A\otimes\mathcal N$.
--
--   Differences from the source:
--   - encoding: finite-dimensional Hilbert spaces and their tensor products → complex matrices indexed by finite types, $\mathcal H_A\otimes\mathcal H_B$ indexed by `A × B` (Kronecker convention); reason: the book works in finite dimensions throughout; same objects.
--   - encoding: quantum channel N (linear, completely positive, trace preserving) → `WildeQIT.QChannel` (finite Kraus family with Σ V†V = I); reason: Theorem 4.4.1 of the book, every channel has this form.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 11.9.3, eq. (11.191), p. 351

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_QChannel
import Definitions.Def_WildeQIT_QMemory_coherentInfo
import Definitions.Def_WildeQIT_QMemory_idTensorChannel

namespace WildeQIT.QMemory

/-- **Theorem 11.9.3 (Data Processing for Coherent Information)** (Wilde, *From Classical to
Quantum Shannon Theory*, arXiv:1106.1445v8, p. 351). For `ρ_AB ∈ D(H_A ⊗ H_B)` and a quantum
channel `N : L(H_B) → L(H_B′)`, with `σ_AB′ ≡ N_{B→B′}(ρ_AB)`, `I(A⟩B)_ρ ≥ I(A⟩B′)_σ` (11.191).

**Formalization Note** The channel is the published `WildeQIT.QChannel` (Choi–Kraus form,
Theorem 4.4.1), acting on `B` as `id_A ⊗ N` (`idTensorChannel`). -/
theorem theorem_11_9_3 {A B B' : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype B'] [DecidableEq B'] (ρ : Matrix (A × B) (A × B) ℂ)
    (hρ : WildeQIT.IsDensityOperator ρ) (N : WildeQIT.QChannel B B') :
    coherentInfo (idTensorChannel N ρ) ≤ coherentInfo ρ := by sorry

end WildeQIT.QMemory
