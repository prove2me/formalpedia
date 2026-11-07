-- Prove2me | Theorems.Thm_SelfCorrect3D_Memory_memory_criterion
-- name    : SelfCorrect3D.Memory.memory_criterion
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:37:27.144195+00:00
-- url     : https://prove2.me/theorems/39a2438b-8af5-49c5-8b86-5d2390663521
-- title:
--   Theorem 2.6 — memory criterion (Chesi–Loss–Bravyi–Terhal), eq. (48)
-- statement:
--   Let $C$ be a CSS code with one logical qubit, together with logical operators $X_L,Z_L$, a decoder $(f_Z,f_X)$ and a code isometry $V$. Let $\mathcal E$ be a set of operators and $\mathcal L$ the Lindbladian of jump operators $S_1,\dots,S_m\in\mathcal E$, with the Gibbs state as stationary state, $\mathcal L(\rho_\beta)=0$. Let $\widetilde X_L,\widetilde Z_L$ be the dressed observables (46) and $P=P_{\mathrm{stable}}$ an orthogonal projector such that
--
--   1. $P\widetilde X_L=\widetilde X_LP$ and $P\widetilde Z_L=\widetilde Z_LP$;
--   2. $\widetilde X_L,\widetilde Z_L$ are protected from $\mathcal E$ on $P$: $[E,\widetilde X_L]P=[E,\widetilde Z_L]P=0$ for all $E\in\mathcal E$ (Definition 2.4);
--   3. $\widetilde X_L$, $\widetilde Z_L$ and $P$ commute with $H$.
--
--   Then the thermal encoding $\mathrm{Enc}_\beta$ is CPTP, and for every single-qubit density matrix $\tau$ and every $t\ge0$,
--
--   $$\bigl\|e^{-it[H,\cdot]+\mathcal Lt}\circ\mathrm{Enc}_\beta(\tau)-\mathrm{Enc}_\beta(\tau)\bigr\|_1\le 8\,\|\mathcal L\|_1\,t\,\mathrm{Tr}\bigl((1-P)\rho_\beta\bigr),$$
--
--   and $\mathrm{Dec}\circ\mathrm{Enc}_\beta(\tau)=\tau$.
--
--   This criterion converts a bound on the Gibbs weight of unstable configurations into a lower bound on the memory lifetime (Corollary 5.14).
--
--   Differences from the source:
--   - generalization: there exists a CPTP logical encoding map Enc and a logical decoding map Dec → the thermal encoding Enc_β of eq. (49) and Dec = Tr_syn in the frame of the given decoder; reason: the paper fixes these ("The proof of this theorem provides explicit logical encoding and logical decoding maps … We choose a thermal encoding map", p. 21); the explicit pair witnesses the existential
--   - encoding: ‖𝓛‖₁ → superNorm of the dissipator, the trace-norm-induced operator norm; reason: the norm of eq. (48); finite and attained in finite dimension
--   - encoding: Tr(1 − P_stable)ρ_β → real part of Tr((1 − P)ρ_β); reason: the trace is real since P and ρ_β are commuting Hermitian operators
--   - encoding: a Lindbladian with jump operators in 𝓔 whose stationary state is ρ_β; the construction has a single encoded qubit (p. 20) → finitely many jumps J_j ∈ 𝓔 for an arbitrary set 𝓔, 𝓛(ρ_β) = 0 for the dissipator, and rank H_x + rank H_z + 1 = n; reason: p. 20 states stationarity as 𝓛(ρ_β) = 0 and restricts the analysis to one encoded qubit; [H, ρ_β] = 0 holds automatically
--   - reading: stabilizer Hamiltonian H → C.hamiltonian = Σ_a (1 − S^X_a)/2 + Σ_b (1 − S^Z_b)/2 over all rows; reason: p. 21 fixes H = I ⊗ H′ with H′ diagonal in the syndrome basis with entries equal to the size of the syndrome, which is this operator, and the thermal encoding (49) is built from it
--   - encoding: a projector P_stable onto a subspace → P with P² = P and Pᴴ = P; reason: a projector onto a subspace of a Hilbert space is the orthogonal one
-- source:
--   Balasubramanian, Davydova, Lin, A passive self-correcting quantum memory in three dimensions, arXiv:2605.10943, Theorem 2.6, eq. (48), p. 21, with eq. (46) and Definitions 2.3–2.4, p. 20, and eq. (49), p. 21

import Mathlib
import Definitions.Def_SelfCorrect3D_Memory_CSSCode_gibbsState
import Definitions.Def_SelfCorrect3D_Memory_evolution
import Definitions.Def_SelfCorrect3D_Memory_superNorm
import Definitions.Def_SelfCorrect3D_Memory_dressedX
import Definitions.Def_SelfCorrect3D_Memory_dressedZ
import Definitions.Def_SelfCorrect3D_Memory_encoding
import Definitions.Def_SelfCorrect3D_Memory_decoding
import Definitions.Def_SelfCorrect3D_Memory_IsCPTP
open Matrix
open scoped ComplexOrder

namespace SelfCorrect3D.Memory

/-- **Theorem 2.6 (memory criterion; Theorem 1 of Chesi–Loss–Bravyi–Terhal).** Balasubramanian, Davydova, Lin, *A passive self-correcting quantum memory in three dimensions*, arXiv:2605.10943,
Theorem 2.6, eq. (48), p. 21, with Definitions 2.3–2.4 and eq. (46), p. 20, and eq. (49), p. 21.

Let `C` be a CSS code with one logical qubit, with logicals, decoder and code isometry `F`, and let
`𝓛` be the Lindbladian of jump operators `J_j` in a set `𝓔` with stationary Gibbs state
`𝓛(ρ_β) = 0`. Let `P` (= `P_stable`) be an orthogonal projector commuting with the dressed
observables `X̃_L`, `Z̃_L`, on which they are protected from `𝓔` (`[E, X̃_L]P = [E, Z̃_L]P = 0` for
`E ∈ 𝓔`), and assume `X̃_L`, `Z̃_L`, `P` commute with `H`. Then the thermal encoding `Enc_β` is CPTP,
and for every single-qubit density matrix `τ` and `t ≥ 0`,
`‖e^{−it[H,·]+𝓛t} Enc_β(τ) − Enc_β(τ)‖₁ ≤ 8 ‖𝓛‖₁ t Tr((1 − P)ρ_β)` and `Dec(Enc_β(τ)) = τ`.

**Formalization Note.** (generalization) The printed "there exists a CPTP Enc … and Dec" is
made explicit: `Enc_β` is the thermal encoding (49) and `Dec = Tr_{𝓗syn}` in the frame `F` (p. 21:
"The proof of this theorem provides explicit logical encoding and logical decoding maps … We
choose a thermal encoding map"). (encoding) `‖𝓛‖₁` is the trace-norm-induced norm of the
dissipator (`superNorm`); `Tr(1 − P_stable)ρ_β` is the real part of the trace. `𝓔` is an arbitrary
set of operators and `β` any real number. -/
theorem memory_criterion {n mX mZ : ℕ} (C : CSSCode n mX mZ) (hC : C.OneLogicalQubit)
    (F : MemoryFrame C) (E : Set (Op n)) {m : ℕ} (J : Fin m → Op n) (hJ : ∀ j, J j ∈ E)
    (β : ℝ) (hstat : dissipator J (C.gibbsState β) = 0)
    (P : Op n) (hP_proj : P * P = P) (hP_herm : Pᴴ = P)
    (hPX : P * dressedX C F = dressedX C F * P) (hPZ : P * dressedZ C F = dressedZ C F * P)
    (hXH : dressedX C F * C.hamiltonian = C.hamiltonian * dressedX C F)
    (hZH : dressedZ C F * C.hamiltonian = C.hamiltonian * dressedZ C F)
    (hPH : P * C.hamiltonian = C.hamiltonian * P)
    (hprotX : ∀ e ∈ E, (e * dressedX C F - dressedX C F * e) * P = 0)
    (hprotZ : ∀ e ∈ E, (e * dressedZ C F - dressedZ C F * e) * P = 0) :
    IsCPTP (encoding C F β) ∧
      ∀ τ : Matrix (ZMod 2) (ZMod 2) ℂ, τ.PosSemidef → τ.trace = 1 →
        (∀ t : ℝ, 0 ≤ t →
          WildeQIT.traceNorm
              (evolution C.hamiltonian J t (encoding C F β τ) - encoding C F β τ) ≤
            8 * superNorm (dissipator J) * t * (Matrix.trace ((1 - P) * C.gibbsState β)).re) ∧
        decoding C F (encoding C F β τ) = τ := by sorry

end SelfCorrect3D.Memory
