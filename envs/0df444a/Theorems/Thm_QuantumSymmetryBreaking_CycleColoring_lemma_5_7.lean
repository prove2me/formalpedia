-- Prove2me | Theorems.Thm_QuantumSymmetryBreaking_CycleColoring_lemma_5_7
-- name    : QuantumSymmetryBreaking.CycleColoring.lemma_5_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:25:24.34269+00:00
-- url     : https://prove2.me/theorems/42ff797e-be05-4ab9-858b-ebd3bb04306a
-- title:
--   Lemma 5.7 — asymptotically orthogonal involutive representations of $G$
-- statement:
--   For every integer $s\ge1$ there is a sequence of matrix families $(\{U^{(N)}_i\in\mathbb C^{N\times N}\}_{i\in[s]})_{N\in\mathbb N_+}$ such that:
--
--   1. (U1) for every $N\in\mathbb N_+$ and $i\in[s]$, $(U^{(N)}_i)^\dagger=U^{(N)}_i$ and $(U^{(N)}_i)^2=I_N$;
--   2. (U2) writing $U^{(N)}_g=U^{(N)}_{i_1}\cdots U^{(N)}_{i_k}$ for $g=g_{i_1}\cdots g_{i_k}\in G$ and $U^{(N)}_e=I_N$, for every fixed $g,h\in G$
--   $$
--   \frac1N\operatorname{Tr}\bigl((U^{(N)}_g)^\dagger U^{(N)}_h\bigr)\longrightarrow\mathbf 1_{g=h}\qquad(N\to\infty).
--   $$
--
--   These are finite-dimensional unitary representations of $G$ whose distinct elements become orthogonal in normalized Frobenius inner product, so that evaluating a fixed polynomial of $\mathbb C[G\times G]$ at them approximately preserves its Frobenius norm.
--
--   Differences from the source:
--   - encoding: $U_g$ for $g=g_{i_1}\cdots g_{i_k}$, and (U2) for all $g,h\in G$ → (U2) for all words $w,w'$ in the generators, with $\mathbf 1$ of `wordProd w = wordProd w'`, and $U_w$ the product along $w$; reason: every $g$ is spelled by some word, and (U1) makes $U_w$ depend only on the element spelled; quantifying over all words is the same claim
--   - encoding: a sequence indexed by $N\in\mathbb N_+$ → a sequence indexed by all $N\in\mathbb N$, (U1) required for $N\ge1$; reason: the entry at $N=0$ is unconstrained and does not affect the limit
--   - encoding: generators indexed by $[s]=\{1,\dots,s\}$ → generators indexed by `Fin s` = $\{0,\dots,s-1\}$; reason: relabelling only
--   - encoding: $G=\langle g_1,\dots,g_s\mid g_i^2=e\rangle$ with word length $|g|$ → the universal Coxeter group on `Fin s` (Coxeter matrix with off-diagonal entries 0, Mathlib's encoding of $\infty$) with its Coxeter length; reason: the same presentation; Coxeter length is the reduced-word length
-- source:
--   Flin, Li, Suomela, Quantum Advantage for Distributed Symmetry Breaking, STOC 2027 submission #863 (October 2026), source.pdf SHA-256 121c1ecfd6ed3365b5424f6f5978549d12510d800fb87cb8d2f5e110600a542e, Lemma 5.7, p.23 (PDF p.26)

import Mathlib
import Definitions.Def_QuantumSymmetryBreaking_CycleColoring_InfiniteConstruction
import Definitions.Def_QuantumSymmetryBreaking_CycleColoring_FiniteRealization

open Filter Topology Matrix

namespace QuantumSymmetryBreaking.CycleColoring

open Classical in
/-- Lemma 5.7, Flin, Li, Suomela, *Quantum Advantage for Distributed Symmetry Breaking*, STOC 2027 submission #863 (October 2026), p.23 (PDF p.26).
For every `s ≥ 1` there is a sequence of matrix families `({U_i^{(N)} ∈ ℂ^{N×N}}_{i ∈ [s]})_{N ∈ ℕ⁺}` with
(U1) `(U_i^{(N)})† = U_i^{(N)}` and `(U_i^{(N)})^2 = I_N` for every `N ≥ 1`, `i ∈ [s]`; and
(U2) for `g = g_{i_1} ⋯ g_{i_k}`, `U_g^{(N)} = U_{i_1}^{(N)} ⋯ U_{i_k}^{(N)}`, and every fixed `g, h ∈ G`,
`(1/N) Tr((U_g^{(N)})† U_h^{(N)}) → 1_{g = h}` as `N → ∞`. Here (U2) is stated for all words `w, w′`
in the generators, with `g, h` the group elements they spell. -/
theorem lemma_5_7 (s : ℕ) (hs : 1 ≤ s) :
    ∃ U : (N : ℕ) → Fin s → Matrix (Fin N) (Fin N) ℂ,
      (∀ N : ℕ, 1 ≤ N → ∀ i : Fin s, (U N i)ᴴ = U N i ∧ U N i ^ 2 = 1) ∧
      ∀ w w' : List (Fin s),
        Tendsto (fun N : ℕ => (1 / (N : ℂ)) * Matrix.trace ((wordMat (U N) w)ᴴ * wordMat (U N) w'))
          atTop (𝓝 (if (coxMat s).toCoxeterSystem.wordProd w = (coxMat s).toCoxeterSystem.wordProd w'
            then 1 else 0)) := by sorry

end QuantumSymmetryBreaking.CycleColoring
