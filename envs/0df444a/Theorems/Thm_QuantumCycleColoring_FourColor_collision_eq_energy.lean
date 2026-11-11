-- Prove2me | Theorems.Thm_QuantumCycleColoring_FourColor_collision_eq_energy
-- name    : QuantumCycleColoring.FourColor.collision_eq_energy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T18:01:10.343859+00:00
-- url     : https://prove2.me/theorems/a246661a-6635-4953-8404-27b57c738f27
-- title:
--   §6.1: the collision probability of colour $i$ equals $\mathcal E_\Lambda(P_i)$
-- statement:
--   Let $q\ge2$, let $\Lambda$ be a PSD $N\times N$ matrix with $\|\Lambda\|_F=1$, and let $\{P_i\}_{i\in[q]}$ be a $q$-outcome POVM on $\mathbb C^N\otimes\mathbb C^N$. Consider the algorithm in which every node prepares $|\Psi\rangle=\mathrm{vec}(\bar\Lambda)$ and measures $\{P_i\}$ on $B_{\ell-1}A_\ell$. On every directed $n$-cycle with $n\ge3$, for every node $\ell$ and every colour $i$,
--   $$\Pr[c_\ell=c_{\ell+1}=i]=\mathcal E_\Lambda(P_i),$$
--   where the left side is the marginal of the Born-rule output distribution of all $n$ nodes.
--
--   Summing over $i$ turns the per-edge collision probability of an algorithm into the total $\Lambda$-energy of its POVM.
--
--   Differences from the source:
--   - encoding: Λ-mass m_Λ(P) = Tr(P(Λ²⊗Λ̄²)) and Λ-energy E_Λ(P) = Tr(ΛAΛB), complex traces that are real for PSD P, Λ → mass Λ P and energy Λ P are the real parts of these traces; reason: the traces are real for PSD P and Λ, so the values are the same
--   - encoding: ℂ^N with its standard basis, operators on ℂ^N ⊗ ℂ^N → vectors indexed by an arbitrary finite type d (N = card d), operators are matrices indexed by d × d with the Kronecker product for ⊗; reason: relabelling the standard basis; the same instances
--   - encoding: directed n-cycle with nodes v_i, i ∈ ℤ_n, n ≥ 3 → nodes ZMod n with an instance NeZero n (needed to sum over the finite set of node labels) and the hypothesis 3 ≤ n; reason: NeZero n is implied by 3 ≤ n; the same cycles
--   - encoding: Pr[c_ℓ = c_{ℓ+1} = i], computed in the paper from the joint state σ of the four registers B_{ℓ−1}A_ℓB_ℓA_{ℓ+1} → the sum of outputProb over all colour vectors c with c ℓ = i and c (ℓ+1) = i, i.e. the marginal of the full n-node output law; reason: the literal meaning of the probability; the paper's σ is how it is computed
-- source:
--   Tom Gur, Longcheng Li, STOC 2027 submission #515 (October 2026), §6.1, proof of Theorem 6.1, display on p.41

import Mathlib
import Definitions.Def_FuchsVdGraaf_IsPOVM
import Definitions.Def_QuantumCycleColoring_FourColor_MatrixAnalysis
import Definitions.Def_QuantumCycleColoring_FourColor_CycleAlgorithm

open scoped Kronecker ComplexOrder

namespace QuantumCycleColoring.FourColor

open Matrix Filter Topology

/-- §6.1, proof of Theorem 6.1, display on p.41 (Gur–Li, STOC 2027 #515): for the normal-form
algorithm with state `|Ψ⟩ = vec(Λ̄)` (PSD `Λ`, `‖Λ‖_F = 1`) and a `q`-outcome POVM (`q ≥ 2`) `{P_i}` on
`ℂ^d ⊗ ℂ^d`, on every directed `n`-cycle with `n ≥ 3`, for every node `ℓ` and colour `i`,
`Pr[c_ℓ = c_{ℓ+1} = i] = E_Λ(P_i)`, the left side being the marginal of the Born-rule output
distribution of all `n` nodes. -/
theorem collision_eq_energy (q : ℕ) (hq : 2 ≤ q) {d : Type} [Fintype d] [DecidableEq d]
    (Λ : Matrix d d ℂ) (hΛ : Λ.PosSemidef) (hΛF : frobNorm Λ = 1)
    (P : Fin q → Matrix (d × d) (d × d) ℂ) (hP : FuchsVdGraaf.IsPOVM P)
    (n : ℕ) [NeZero n] (hn : 3 ≤ n) (ℓ : ZMod n) (i : Fin q) :
    ∑ c ∈ Finset.univ.filter (fun c : ZMod n → Fin q => c ℓ = i ∧ c (ℓ + 1) = i),
        outputProb n (vecConjState Λ) P c = energy Λ (P i) := by sorry

end QuantumCycleColoring.FourColor
