-- Prove2me | Theorems.Thm_SYKEdge_fact_3_1
-- name    : SYKEdge.fact_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:06:53.396194+00:00
-- url     : https://prove2.me/theorems/502efe9c-c248-47e3-8585-cdce27caa22a
-- title:
--   Fact 3.1 — Johnson eigenspaces: $\mathbb C^{\binom{[n]}k}=\bigoplus_{j=0}^kV_j$, $\dim V_j=\binom nj-\binom n{j-1}$, $M_t|_{V_j}=\mu_{t,j}\mathrm{Id}$, $S_n$-invariance
-- statement:
--   Let $0\le k\le n/2$ and $M_t(S,T)=\binom{|S\cap T|}t$ on $\binom{[n]}k$. There is an orthogonal decomposition
--   $$\mathbb C^{\binom{[n]}k}=\bigoplus_{j=0}^kV_j$$
--   such that, for all $0\le j,t\le k$:
--
--   1. $\dim V_j=\binom nj-\binom n{j-1}$ (with $\binom n{-1}=0$), and $V_0=\operatorname{span}\{\mathbf 1\}$;
--   2. $M_t$ acts on $V_j$ as the scalar $\mu_{t,j}=\binom{k-j}{t-j}\binom{n-t-j}{k-t}$ for $j\le t$, and $0$ for $j>t$;
--   3. each $V_j$ is invariant under the action $(\sigma\cdot\psi)(S)=\psi(\sigma^{-1}(S))$ of the symmetric group $S_n$.
--
--   This is the classical spectral decomposition of the Johnson scheme (Delsarte, Wilson), cited by the paper; it diagonalizes the dense sign matrix.
--
--   **Formalization Note** Orthogonality is for the standard Hermitian inner product of $\mathbb C^{\binom{[n]}k}$; with pairwise orthogonality, "the subspaces span the whole space" makes the sum direct.
--
--   Differences from the source:
--   - encoding: an orthogonal decomposition ⊕_{j=0}^{k} V_j → V : Fin (k+1) → subspaces, pairwise orthogonal, with ⨆_j V_j = ⊤; reason: pairwise orthogonal subspaces whose sum is everything form an orthogonal direct-sum decomposition
--   - encoding: k ⩽ n/2; dim(V_j) for all j ⩾ 0 → 2k ⩽ n; the dimension formula for 0 ⩽ j ⩽ k; reason: the same condition on natural numbers; V_j exists only for j ⩽ k
-- source:
--   Basu, Kothari, Midha, Sharp Bounds on Ground State Energy of the SYK Model, arXiv:2607.27185v2, Fact 3.1, p.16

import Mathlib
import Definitions.Def_SYKEdge_Johnson
open Matrix

namespace SYKEdge

/-- **Fact 3.1** (Johnson eigenspaces, [Del73, Wil90]), A. Basu, P. K. Kothari, S. Midha, *Sharp Bounds on Ground State Energy of the SYK Model*,
arXiv:2607.27185v2, p.16.

For `0 ⩽ j, t ⩽ k ⩽ n/2` there is an orthogonal decomposition `ℂ^{([n] choose k)} = ⊕_{j=0}^{k} V_j`
such that each `V_j` is an eigenspace of every `M_t`, and
(1) `dim V_j = (n choose j) − (n choose j−1)` (with `(n choose −1) := 0`), and `V₀ = span{1}`;
(2) `M_t|_{V_j} = μ_{t,j} Id_{V_j}`;
(3) each `V_j` is invariant under the action `(σ·ψ)(S) = ψ(σ^{−1}(S))` of `S_n`.

**Formalization Note.** `k ⩽ n/2` is `2k ⩽ n`. Orthogonality is for the standard inner product
`⟨v, w⟩ = Σ_S conj(v_S) w_S`; with pairwise orthogonality, `⨆_j V_j = ⊤` makes the sum direct and equal
to the whole space. `1` is the all-ones vector. -/
theorem fact_3_1 (n k : ℕ) (hk : 2 * k ≤ n) :
    ∃ V : Fin (k + 1) → Submodule ℂ (KSet n k → ℂ),
      (∀ j j' : Fin (k + 1), j ≠ j' → ∀ v ∈ V j, ∀ w ∈ V j', star v ⬝ᵥ w = 0) ∧
      (⨆ j, V j) = ⊤ ∧
      (∀ j : Fin (k + 1), Module.finrank ℂ (V j) = dJ n j) ∧
      V 0 = Submodule.span ℂ {fun _ => (1 : ℂ)} ∧
      (∀ j : Fin (k + 1), ∀ t : ℕ, t ≤ k → ∀ v ∈ V j,
        johnsonM n k t *ᵥ v = ((muTJ n k t j : ℕ) : ℂ) • v) ∧
      (∀ j : Fin (k + 1), ∀ σ : Equiv.Perm (Fin n), ∀ v ∈ V j, permAct σ v ∈ V j) := by sorry

end SYKEdge
