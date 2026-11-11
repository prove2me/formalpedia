-- Prove2me | Theorems.Thm_QuantumCycleColoring_FourColor_normal_form_eq_26
-- name    : QuantumCycleColoring.FourColor.normal_form_eq_26
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T18:01:09.528321+00:00
-- url     : https://prove2.me/theorems/7bd0167f-670b-46ab-83a8-0960d14c28c0
-- title:
--   §6.1, eq. (26): every one-way one-round algorithm has the normal form $\mathrm{vec}(\bar\Lambda)$
-- statement:
--   Let $q\ge2$. Every one-way one-round anonymous quantum $q$-colouring algorithm — every node prepares a state $\rho$ on registers $A_\ell B_\ell$, sends $B_\ell$ to its successor and measures a $q$-outcome POVM $\{P_i\}$ on $B_{\ell-1}A_\ell$ — can be put in the following normal form without changing its behaviour: there are a local dimension $N$, a PSD $N\times N$ matrix $\Lambda$ with $\|\Lambda\|_F=1$ and a $q$-outcome POVM $\{P'_i\}$ on $\mathbb C^N\otimes\mathbb C^N$ such that, when every node instead prepares
--   $$|\Psi\rangle=\mathrm{vec}(\bar\Lambda)\in\mathbb C^N\otimes\mathbb C^N$$
--   and measures $\{P'_i\}$ on $B_{\ell-1}A_\ell$, the output distribution on every directed $n$-cycle, $n\ge3$, is the same as before.
--
--   The normal form is what turns statements about algorithms into statements about a single weight matrix $\Lambda$ and a POVM.
--
--   Differences from the source:
--   - generalization: an algorithm in the normal form of §6.1 (every node prepares a pure state |Ψ⟩ on ℂ^N ⊗ ℂ^N and measures a POVM on ℂ^N ⊗ ℂ^N), to which Definition 3.10's arbitrary finite algorithm is reduced → every node prepares an arbitrary density matrix ρ on A × B (arbitrary finite index types a, b) and measures an arbitrary POVM on B × A (received B, own A); the output law is the Born rule of the whole n-node experiment; reason: contains the normal form (a = b = Fin N, ρ = |vec Λ̄⟩⟨vec Λ̄|) and every finite-dimensional one-way one-round algorithm of Definition 3.10, with private randomness and workspace absorbed into A and the mixed state ρ
--   - encoding: directed n-cycle with nodes v_i, i ∈ ℤ_n, n ≥ 3 → nodes ZMod n with an instance NeZero n (needed to sum over the finite set of node labels) and the hypothesis 3 ≤ n; reason: NeZero n is implied by 3 ≤ n; the same cycles
--   - encoding: "we may assume without loss of generality that the shared state is vec(Λ̄)" → existence of N, Λ, P' such that the two algorithms have the same output distribution c ↦ Pr[c] on every n-cycle with n ≥ 3; reason: the precise content of "without loss of generality"; the same N, Λ, P' serve every n
-- source:
--   Tom Gur, Longcheng Li, STOC 2027 submission #515 (October 2026), §6.1, proof of Theorem 6.1, eq. (26), p.41

import Mathlib
import Definitions.Def_FuchsVdGraaf_IsPOVM
import Definitions.Def_QuantumCycleColoring_FourColor_MatrixAnalysis
import Definitions.Def_QuantumCycleColoring_FourColor_CycleAlgorithm

open scoped Kronecker ComplexOrder

namespace QuantumCycleColoring.FourColor

open Matrix Filter Topology

/-- §6.1, proof of Theorem 6.1, eq. (26), p.41 (Gur–Li, STOC 2027 #515), for every `q ≥ 2`:
every one-way one-round anonymous algorithm (state `ρ` on `A × B`, `q`-outcome POVM `P` on
`B_{ℓ-1} A_ℓ`) has the normal form in which every node prepares `|Ψ⟩ = vec(Λ̄) ∈ ℂ^N ⊗ ℂ^N` for a
PSD `Λ` with `‖Λ‖_F = 1` and measures a `q`-outcome POVM `P'` on `ℂ^N ⊗ ℂ^N`: the two algorithms
have the same output distribution on every directed `n`-cycle, `n ≥ 3`. -/
theorem normal_form_eq_26 (q : ℕ) (hq : 2 ≤ q) (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (ρ : Matrix (a × b) (a × b) ℂ) (hρ : IsDensityMatrix ρ)
    (P : Fin q → Matrix (b × a) (b × a) ℂ) (hP : FuchsVdGraaf.IsPOVM P) :
    ∃ (N : ℕ) (Λ : Matrix (Fin N) (Fin N) ℂ) (P' : Fin q → Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ),
      Λ.PosSemidef ∧ frobNorm Λ = 1 ∧ FuchsVdGraaf.IsPOVM P' ∧
      ∀ (n : ℕ) [NeZero n], 3 ≤ n → ∀ c : ZMod n → Fin q,
        outputProb n ρ P c = outputProb n (vecConjState Λ) P' c := by sorry

end QuantumCycleColoring.FourColor
