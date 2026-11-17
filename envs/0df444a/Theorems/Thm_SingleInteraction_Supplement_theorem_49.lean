-- Prove2me | Theorems.Thm_SingleInteraction_Supplement_theorem_49
-- name    : SingleInteraction.Supplement.theorem_49
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:07:17.048919+00:00
-- url     : https://prove2.me/theorems/b6d7aa11-b057-4f1c-9cd4-c6bf89fd1785
-- title:
--   Theorem 49 — exact low-energy preservation of the unpinned compiler of eq. (28), $\Delta=2J+\gamma$
-- statement:
--   Let $A=\{h^{(1)},\dots,h^{(m)}\}$ be $k$-qubit Hermitian interactions with distinct binary tags of length $\ell=\lceil\log_2m\rceil$, let $J=\max_j\|h^{(j)}\|$, and let $K=\sum_{i=1}^Mh^{(j_i)}_{V_i}$ on a working register $W$, with ordered $k$-tuples $V_i$ of distinct qubits and **no** distinctness assumption on the pairs $(V_i,j_i)$. Fix $\gamma>0$, set $\Delta=2J+\gamma$, and let $\tilde K$ be the compiled Hamiltonian of eq. (28) with a dedicated block of $\ell+1$ auxiliary pairs per occurrence. With $V|\psi\rangle=|\psi\rangle\otimes|\Omega\rangle_A$, $|\Omega\rangle_A=|01\rangle^{\otimes M(\ell+1)}$ and $E_0=\lambda_{\min}(K)$:
--
--   1. $\mathrm{im}(V)$ is invariant under $\tilde K$, and $V^\dagger\tilde KV=K$;
--   2. $\tilde K(z)\succeq K+\gamma I$ for every invalid computational-basis auxiliary sector $z$;
--   3. $\mathrm{Ground}(\tilde K)=V\,\mathrm{Ground}(K)$;
--   4. every eigenvalue of $K$ strictly below $E_0+\gamma$ appears in $\tilde K$ with exactly the same multiplicity, and $\tilde K$ has no other eigenvalue below this cutoff;
--   5. $\lambda_{\min}(\tilde K)=\lambda_{\min}(K)$;
--   6. if $K$ has a spectral gap $\delta>0$ above its ground space and $\tilde\delta$ is the gap of $\tilde K$, then $\min\{\delta,\gamma\}\le\tilde\delta\le\delta$, and $\tilde\delta=\delta$ if $\gamma\ge\delta$.
--
--   The interaction acts on $k+\ell+2$ qubits. The compiler removes the pinning resource while preserving the low-energy spectrum exactly, so Local Hamiltonian thresholds carry over unchanged.
--
--   **Formalization Note** Multiplicities are characteristic-polynomial root multiplicities. The tag map is any injective map; $J$ is the maximum of operator norms.
--
--   Differences from the source:
--   - generalization: a fixed finite set A = {h(1), …, h(m)} → an indexed family A : Fin m → k-qubit Hermitian matrices, members possibly repeated; reason: a set is the case of an injective enumeration; the paper itself treats members differing by a scalar as distinct elements (p.36)
--   - encoding: for each h(j) choose a distinct binary string x(j) → every injective tag map Fin m → {0,1}^ℓ; reason: the theorem holds for any such choice, which is what the paper asserts
--   - encoding: in the r-th application the r-th pair occupies the check positions and the remaining ℓ pairs encode the tag (p.40) → selector position s uses pair r.succAbove s, taking the first qubit for tag bit 0 and the second for tag bit 1; reason: this is the routing of §4.1.1 and p.40 that makes the valid configuration (01)^{M(ℓ+1)} spell the tag
--   - encoding: im(V) invariant under K̃ → K̃V = V(V†K̃V); reason: equivalent for an isometry V
--   - encoding: K has spectral gap δ > 0 above its ground space; δ̃ the gap of K̃ → K has an eigenvalue above λmin(K); δ and δ̃ are specGap of K and K̃; reason: the gap is positive exactly when an eigenvalue lies above λmin
-- source:
--   Hecker, The Complexity of Single-Interaction Hamiltonians, arXiv:2609.39592 (held version, sha256 19ddc444…), Theorem 49, p.40-41

import Mathlib
import Definitions.Def_SingleInteraction_onTuple
import Definitions.Def_SingleInteraction_Supplement_Linalg
import Definitions.Def_SingleInteraction_Supplement_Compiler

open Matrix
open scoped ComplexOrder

namespace SingleInteraction

namespace Supplement

/-- Theorem 49 (Exact Low-Energy Preservation of the Single-Interaction Compiler) (Hecker, *The
Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…),
§4.2.2, pp.40–41).

Let `A = {h(1), …, h(m)}` be `k`-qubit Hermitian interactions with distinct binary tags of length
`ℓ = ⌈log₂ m⌉`, `J = max_j ‖h(j)‖`, and `K = Σ_{i=1}^M h(j_i)_{V_i}` on a working register `W`, with
no distinctness assumption on the pairs `(V_i, j_i)`. Fix `γ > 0`, `∆ = 2J + γ`, and let `K̃` be the
compiled Hamiltonian built from eq. (28) with a dedicated block of `ℓ + 1` auxiliary pairs per
occurrence. With `V|ψ⟩ = |ψ⟩ ⊗ |Ω⟩_A`, `|Ω⟩_A = |01⟩^{⊗M(ℓ+1)}` and `E₀ = λmin(K)`:
1. `im V` is invariant under `K̃` and `V†K̃V = K`;
2. `K̃(z) ⪰ K + γI` for every invalid computational-basis auxiliary sector `z`;
3. `Ground(K̃) = V Ground(K)`;
4. every eigenvalue of `K` strictly below `E₀ + γ` appears in `K̃` with the same multiplicity, and
   `K̃` has no other eigenvalue below that cutoff;
5. `λmin(K̃) = λmin(K)`;
6. if `K` has a spectral gap `δ > 0` above its ground space and `δ̃` is that of `K̃`, then
   `min{δ, γ} ≤ δ̃ ≤ δ`, and `δ̃ = δ` if `γ ≥ δ`.
The interaction acts on `k + ℓ + 2` qubits.

**Formalization Note** The construction is `compHam` (see `Def_SingleInteraction_Supplement_Compiler`)
for an arbitrary injective tag map. Item 1's invariance is `K̃ V = V (V† K̃ V)`. Item 2 is positive
semidefiniteness of `K̃(z) − K − γI`. Item 4 is stated with characteristic-polynomial multiplicities,
which covers "no additional eigenvalues" (multiplicity `0` stays `0`). Item 6's hypothesis "`K` has a
spectral gap above its ground space" is that `K` has an eigenvalue above `λmin(K)`; `δ = specGap K`
is then positive. The locality `k + ℓ + 2` is the type of `hUnp`. -/
theorem theorem_49 (k m NW M : ℕ) (A : Fin m → Matrix (Fin k → Fin 2) (Fin k → Fin 2) ℂ)
    (hA : ∀ j, (A j).IsHermitian) (tag : Fin m → Fin (selLen m) → Fin 2)
    (htag : Function.Injective tag) (V : Fin M → Fin k → Fin NW)
    (hV : ∀ i, Function.Injective (V i)) (jj : Fin M → Fin m) (γ : ℝ) (hγ : 0 < γ) :
    let K := targetHam A V jj
    let Kt := compHam A tag (2 * maxNorm A + γ) V jj
    let W := validIso NW M m
    (Kt * W = W * (Wᴴ * Kt * W) ∧ Wᴴ * Kt * W = K) ∧
      (∀ z, z ≠ zVal M m → (sectorOp Kt z - K - (γ : ℂ) • 1).PosSemidef) ∧
      groundSpace Kt = (groundSpace K).map (Matrix.toEuclideanLin W) ∧
      (∀ μ : ℝ, μ < lamMin K + γ → eigMult Kt μ = eigMult K μ) ∧
      lamMin Kt = lamMin K ∧
      ((excited K).Nonempty →
        min (specGap K) γ ≤ specGap Kt ∧ specGap Kt ≤ specGap K ∧
          (specGap K ≤ γ → specGap Kt = specGap K)) := by sorry

end Supplement

end SingleInteraction
