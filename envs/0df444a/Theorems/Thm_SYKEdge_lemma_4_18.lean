-- Prove2me | Theorems.Thm_SYKEdge_lemma_4_18
-- name    : SYKEdge.lemma_4_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:08:41.558896+00:00
-- url     : https://prove2.me/theorems/91f03915-654d-4bae-9e6f-5839555f9e2b
-- title:
--   Lemma 4.18 — $\mathbb E\|H^{\mathcal H}_{SYK}\|_{op}\ge\lambda_{\max}(\Pi_Rx\Pi_R)-O(1)\sqrt{L(\rho^++\delta)/(1-q)}$
-- statement:
--   Let $n\ge k\ge2$ be even integers with $\alpha=k^2/n<1/16$, let $\mathcal H$ be a $k$-uniform hypergraph with leakage parameters $q,\delta,\rho^+$, and let $H^{\mathcal H}_{SYK}$ be its SYK Hamiltonian on Majorana operators of dimension $2^{n/2}$. Let $R=R_{t_0,M}$ be a Krylov space (Definition 4.11) and $L=t_0+M$. Then
--   $$\mathbb E\|H^{\mathcal H}_{SYK}\|_{op}\ \ge\ \lambda_{\max}(\Pi_Rx\Pi_R)-O(1)\cdot\sqrt{\frac{L(\rho^++\delta)}{1-q}},$$
--   and the same lower bound holds for $\mathbb E\lambda_{\max}(H^{\mathcal H}_{SYK})$.
--
--   This transfers the Krylov witness of Lemma 4.12 to the SYK Hamiltonian at an additive cost controlled by the leakage parameters.
--
--   **Formalization Note** $O(1)$ is an absolute constant chosen before $n,k$, the hypergraph, $t_0,M$ and the Majorana family.
--
--   Differences from the source:
--   - encoding: the §3 standing assumptions (n ⩾ k ⩾ 2 even, ℋ a k-uniform hypergraph) → IsKUniform n k m S: the same, with ℋ = (S_1, …, S_m) an indexed list and m ⩾ 1; reason: repeated hyperedges are distinct elements (footnote 6); m ⩾ 1 is needed for |ℋ|^{−1/2} and only excludes the empty hypergraph
--   - encoding: an arbitrary irreducible unitary representation of the Majorana relations on C^N, N = 2^{n/2} (p.15, footnote 14) → every family γ : Fin n → Matrix ι ι ℂ with card ι = 2^{n/2} satisfying the three Majorana relations; reason: for even n the complex Clifford algebra on n generators is the full matrix algebra of size 2^{n/2}, so these families are exactly the irreducible representations; they are unitarily equivalent and share every spectral quantity
--   - encoding: O(1) in the error term → one absolute constant C > 0 quantified before n, k, the representation and the family; reason: the paper's O(1) are absolute constants (footnote 20, p.36)
--   - generalization: the lower bound stated for ‖H‖_op → the lower bound stated for ‖H‖_op and, as a second conjunct, for λ_max(H); reason: Remark 1.2(1) and footnote 4 (pp.2–3) assert that the argument applies to λ_max; dropping the conjunct gives the printed statement
--   - encoding: no hypothesis on q printed → q < 1; reason: for q = 1 the error term √(L(ρ⁺+δ)/(1−q)) is undefined; q < 1 is also the hypothesis of Lemma 4.17, which the proof applies
--   - encoding: R any space of the kind of Definition 4.11 → R = R_{t₀,M} with M ⩾ 1, and L := t₀ + M; reason: for M = 0, R = {0} has no unit vector and λ_max(Π_R x Π_R) is undefined; L is the L of Lemma 4.12 (proof of Lemma 4.18, p.33)
-- source:
--   Basu, Kothari, Midha, Sharp Bounds on Ground State Energy of the SYK Model, arXiv:2607.27185v2, Lemma 4.18, p.32; footnote 4, p.3

import Mathlib
import Definitions.Def_SYKEdge_Krylov
import Definitions.Def_SYKEdge_Hamiltonian
import Definitions.Def_SYKEdge_MatrixNorms
open Matrix MeasureTheory

namespace SYKEdge

/-- **Lemma 4.18** (Lower Bounds on Operator Norm of the SYK Hamiltonian), A. Basu, P. K. Kothari, S. Midha, *Sharp Bounds on Ground State Energy of the SYK Model*,
arXiv:2607.27185v2, p.32;
the `λ_max` form from footnote 4, p.3.

Let `n ⩾ k ⩾ 2` be even integers, `α := k²/n < 1/16`, and `H^H_SYK` the SYK Hamiltonian (8) for the
hypergraph `H`. Let `R = R_{t₀,M}` be a space of the kind of Definition 4.11, `L = t₀ + M`. Then
`E‖H^H_SYK‖_op ⩾ λ_max(Π_R x Π_R) − O(1)·√(L(ρ⁺ + δ)/(1 − q))`, and by footnote 4 the same lower bound
holds for `E λ_max(H^H_SYK)`.

**Formalization Note.**
* `O(1)` is an absolute `C > 0` chosen before `n, k, m`, the hypergraph, `t₀, M` and the family.
* `q < 1` is the hypothesis of Lemma 4.17, which the proof applies (for `q = 1` the bound is undefined);
  `M ⩾ 1` (for `M = 0`, `R = 0`).
* Majorana families of dimension `2^{n/2}`; `g ∼ N(0, Id_m)`. -/
theorem lemma_4_18 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n k m : ℕ) (S : Fin m → Finset (Fin n)), IsKUniform n k m S →
        (k : ℝ) ^ 2 / n < 1 / 16 → qParam S < 1 →
        ∀ t₀ M : ℕ, 1 ≤ M →
        ∀ (ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι = 2 ^ (n / 2) →
        ∀ γ : Fin n → Matrix ι ι ℂ, IsMajoranaFamily γ →
          lamMaxOn S (krylovR S t₀ M) -
              C * Real.sqrt (((t₀ + M : ℕ) : ℝ) * (rhoPlus S + deltaParam S) / (1 - qParam S))
            ≤ ∫ g, opNorm (syk γ S g) ∂stdGauss (Fin m) ∧
          lamMaxOn S (krylovR S t₀ M) -
              C * Real.sqrt (((t₀ + M : ℕ) : ℝ) * (rhoPlus S + deltaParam S) / (1 - qParam S))
            ≤ ∫ g, lamMax (syk γ S g) ∂stdGauss (Fin m) := by sorry

end SYKEdge
