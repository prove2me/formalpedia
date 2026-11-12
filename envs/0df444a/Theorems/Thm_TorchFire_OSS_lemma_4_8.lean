-- Prove2me | Theorems.Thm_TorchFire_OSS_lemma_4_8
-- name    : TorchFire.OSS.lemma_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:37:58.819198+00:00
-- url     : https://prove2.me/theorems/a6f82164-03bb-4431-80db-e4245404e852
-- title:
--   Lemma 4.8 — $Q'_y|u\rangle=2^{-(n-r)}\sum_{w\in u+S_y}|w\rangle$ and $Q'_y\Theta_y=|W_y\rangle\langle W_y|$
-- statement:
--   Fix the oracles of Construction 4.2 and a verification key $y$. Let $\Theta_y=\sum_{u\in W_y}|u\rangle\langle u|$, $Q_y=\sum_{v\in S_y^\perp}|v\rangle\langle v|$ and $Q'_y=H^{\otimes k}Q_yH^{\otimes k}$. Then for every $u\in\mathbb Z_2^k$,
--   $$Q'_y|u\rangle=2^{-(n-r)}\sum_{w\in u+S_y}|w\rangle\quad(10),$$
--   and
--   $$\Pi_y:=Q'_y\Theta_y=|W_y\rangle\langle W_y|\quad(11).$$
--
--   The lemma identifies the accepting operator of the public coset test (coset membership through $P^{-1}$, then dual membership through $D$ in the Hadamard basis) with the projector onto the signing state; torch-fire verification of anchors rests on it.
--
--   Differences from the source:
--   - encoding: the construction for λ ≥ 2 → every parameter at max(λ, 2); reason: paper.md decision 7; equal for λ ≥ 2, and negligibility ignores finitely many λ
-- source:
--   Chatterjee, Mukherjee, Pathak, Podder, Quantum Fire with Delegated Cloning, arXiv:2610.03593 (held version, sha256 4e43d2f2…afd593), Lemma 4.8, (10)–(11), p.21

import Mathlib
import Definitions.Def_TorchFire_OSS_Theta
import Definitions.Def_TorchFire_Model_traceDist

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 2048

open Matrix TorchFire.Model

namespace TorchFire.OSS

/-- **Lemma 4.8**, p.21 (Chatterjee–Mukherjee–Pathak–Podder, *Quantum Fire with Delegated Cloning*, arXiv:2610.03593, held version sha256 4e43d2f2…afd593). Fix the oracles of Construction 4.2 and a verification key `y`.
With `Θ_y = Σ_{u ∈ W_y} |u⟩⟨u|`, `Q_y = Σ_{v ∈ S_y^⊥} |v⟩⟨v|` and `Q′_y = H^{⊗k} Q_y H^{⊗k}`: for every
`u ∈ Z_2^k`, `Q′_y |u⟩ = 2^{−(n−r)} Σ_{w ∈ u + S_y} |w⟩` (10), and `Π_y := Q′_y Θ_y = |W_y⟩⟨W_y|` (11). -/
theorem lemma_4_8 (lam : ℕ) (ω : OneSample lam) (y : Bits (r lam)) :
    (∀ u : Bits (k lam), (Qprime ω y).mulVec (ket u) = fun w =>
        if ∃ v : Bits (nr lam), u + (Amat ω y).mulVec v = w then (2 : ℂ)⁻¹ ^ nr lam else 0) ∧
    PiY ω y = ketbra (cosetState ω y) := by sorry

end TorchFire.OSS
