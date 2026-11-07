-- Prove2me | Theorems.Thm_SYKEdge_lemma_4_17
-- name    : SYKEdge.lemma_4_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:07:41.232898+00:00
-- url     : https://prove2.me/theorems/81799b55-ef66-4f3c-b43b-b17b63e000de
-- title:
--   Lemma 4.17 — Lipschitzness $\|H(g)-H(g')\|_{op}\le\sqrt{(\rho^++\delta)/(1-q)}\,\|g-g'\|_2$
-- statement:
--   Let $\mathcal H$ be a $k$-uniform hypergraph with leakage parameters $q,\delta,\rho^+$, assume $q<1$, and let $H(g)=m^{-1/2}\sum_ig_i\Gamma_{S_i}$ on Majorana operators of dimension $2^{n/2}$. For all $g,g'\in\mathbb R^m$,
--   $$\|H(g)-H(g')\|_{op}\le\sqrt{\frac{\rho^++\delta}{1-q}}\;\|g-g'\|_2,$$
--   and the same Lipschitz bound holds for $g\mapsto\lambda_{\max}(H(g))$:
--   $$|\lambda_{\max}(H(g))-\lambda_{\max}(H(g'))|\le\sqrt{\frac{\rho^++\delta}{1-q}}\;\|g-g'\|_2 .$$
--
--   With Gaussian concentration this gives fluctuations of order $\sqrt{(\rho^++\delta)/(1-q)}$ for $\|H\|_{op}$ and $\lambda_{\max}(H)$.
--
--   Differences from the source:
--   - encoding: the §3 standing assumptions (n ⩾ k ⩾ 2 even, ℋ a k-uniform hypergraph) → IsKUniform n k m S: the same, with ℋ = (S_1, …, S_m) an indexed list and m ⩾ 1; reason: repeated hyperedges are distinct elements (footnote 6); m ⩾ 1 is needed for |ℋ|^{−1/2} and only excludes the empty hypergraph
--   - encoding: an arbitrary irreducible unitary representation of the Majorana relations on C^N, N = 2^{n/2} (p.15, footnote 14) → every family γ : Fin n → Matrix ι ι ℂ with card ι = 2^{n/2} satisfying the three Majorana relations; reason: for even n the complex Clifford algebra on n generators is the full matrix algebra of size 2^{n/2}, so these families are exactly the irreducible representations; they are unitarily equivalent and share every spectral quantity
--   - generalization: the Lipschitz bound stated for ‖H‖_op → the Lipschitz bound stated for ‖H‖_op and, as a second conjunct, for λ_max(H); reason: Remark 1.2(1) and footnote 4 (pp.2–3) assert that the argument applies to λ_max; dropping the conjunct gives the printed statement
-- source:
--   Basu, Kothari, Midha, Sharp Bounds on Ground State Energy of the SYK Model, arXiv:2607.27185v2, Lemma 4.17, p.31; footnote 4, p.3

import Mathlib
import Definitions.Def_SYKEdge_Hamiltonian
import Definitions.Def_SYKEdge_SignMatrix
import Definitions.Def_SYKEdge_MatrixNorms
open Matrix

namespace SYKEdge

/-- **Lemma 4.17** (Lipschitzness), A. Basu, P. K. Kothari, S. Midha, *Sharp Bounds on Ground State Energy of the SYK Model*,
arXiv:2607.27185v2, p.31; the `λ_max` form from footnote 4, p.3.

For every `g, g' ∈ ℝ^H`, `‖H(g) − H(g')‖_op ⩽ √((ρ⁺ + δ)/(1 − q))·‖g − g'‖₂`, assuming `q < 1`.
By footnote 4 the same Lipschitz bound holds for `g ↦ λ_max(H(g))`.

**Formalization Note.** `‖·‖₂` is the Euclidean norm on `ℝ^m`. The `λ_max` form is
`|λ_max(H(g)) − λ_max(H(g'))| ⩽ √((ρ⁺ + δ)/(1 − q))·‖g − g'‖₂`. The hypergraph satisfies the §3
standing assumptions and the Majorana family has dimension `2^{n/2}`. -/
theorem lemma_4_17 {n k m : ℕ} (S : Fin m → Finset (Fin n)) (hS : IsKUniform n k m S)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (hι : Fintype.card ι = 2 ^ (n / 2))
    (γ : Fin n → Matrix ι ι ℂ) (hγ : IsMajoranaFamily γ) (hq : qParam S < 1)
    (g g' : Fin m → ℝ) :
    opNorm (syk γ S g - syk γ S g') ≤
      Real.sqrt ((rhoPlus S + deltaParam S) / (1 - qParam S)) *
        Real.sqrt (∑ i, (g i - g' i) ^ 2) ∧
    |lamMax (syk γ S g) - lamMax (syk γ S g')| ≤
      Real.sqrt ((rhoPlus S + deltaParam S) / (1 - qParam S)) *
        Real.sqrt (∑ i, (g i - g' i) ^ 2) := by sorry

end SYKEdge
