-- Prove2me | Theorems.Thm_WildeQIT_Schumacher_property_15_1_2
-- name    : WildeQIT.Schumacher.property_15_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T18:37:03.884149+00:00
-- url     : https://prove2.me/theorems/1c5f4d0d-158d-4583-ad28-d6b63b9fd0a0
-- title:
--   Property 15.1.2 (Exponentially Smaller Dimension): $(1-\varepsilon)2^{n(H(A)-c\delta)} \le \mathrm{Tr}\{\Pi^\delta_{A^n}\} \le 2^{n(H(A)+c\delta)}$
-- statement:
--   There is a positive constant $c$ with the following property. Let $\rho_A$ be a density operator on a finite-dimensional space with spectral decomposition $\rho = \sum_x p_X(x)|x\rangle\langle x|$, let $H(A)_\rho = -\mathrm{Tr}\{\rho\log\rho\}$ be its quantum entropy (bits), and let $\Pi^\delta_{A^n}$ be the $\delta$-typical projector. For every $\delta > 0$:
--
--   1. for every $n$,
--   $$
--   \mathrm{Tr}\{\Pi^\delta_{A^n}\} \le 2^{n(H(A)+c\delta)} ;
--   $$
--   2. for every $\varepsilon \in (0,1)$ there is an $N$ such that for all $n \ge N$
--   $$
--   \mathrm{Tr}\{\Pi^\delta_{A^n}\} \ge (1-\varepsilon)\,2^{n(H(A)-c\delta)} .
--   $$
--
--   $\mathrm{Tr}\{\Pi^\delta_{A^n}\}$ is the dimension of the typical subspace, so it is exponentially smaller than $|A|^n$ unless $\rho$ is maximally mixed. This bounds the size of the compressed system in Schumacher compression.
--
--   **Formalization Note** $c$ is quantified before the system, the state, its decomposition and $\delta$: one constant for all of them ("some positive constant that depends on whether we employ the weak or strong notion of typicality"). $H(A)$ is the published `QAlgorithms.vnEntropy` (base 2). $\mathrm{Tr}$ is the real part of the trace.
--
--   Differences from the source:
--   - reading: weak or strong typicality → weak typicality (Definition 14.2.3); reason: the book's c depends on the notion chosen; Chapter 18 uses the weak typical set of §14.4.
--   - reading: (15.18) stated without a quantifier on n, before "for all ε ∈ (0, 1), δ > 0, and sufficiently large n" → (15.18) for every n; reason: the sentence's quantifiers follow (15.19); the stronger reading for (15.18) holds for weak typicality, and the weaker reading would be a different statement.
--   - reading: "some positive constant c" → one c > 0 uniform in the system, state, decomposition and δ; reason: the book says c depends only on the notion of typicality.
--   - reading: the typical projector of ρ → every spectral decomposition (U, p) of ρ; reason: the decomposition is implicit in the book.
--   - encoding: "sufficiently large n" → ∃ N, ∀ n ≥ N; reason: Lean convention.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Property 15.1.2, eqs. (15.18)–(15.19), p. 467

import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_WildeQIT_Schumacher_IsSpectralDecomposition
import Definitions.Def_WildeQIT_Schumacher_typicalProjector

namespace WildeQIT.Schumacher

/-- **Property 15.1.2 (Exponentially Smaller Dimension)** (Wilde, *From Classical to Quantum
Shannon Theory*, arXiv:1106.1445v8, p. 467, eqs. (15.18)–(15.19)): there is a positive constant
`c` (depending only on the notion of typicality) such that
`Tr{Π^δ_{Aⁿ}} ≤ 2^{n(H(A)+cδ)}` (15.18), and
`Tr{Π^δ_{Aⁿ}} ≥ (1 − ε) 2^{n(H(A)−cδ)}` (15.19) for all `ε ∈ (0, 1)`, `δ > 0` and sufficiently
large `n`.

**Formalization Note.** `c` is quantified before the system, the state, its spectral
decomposition and `δ`: one constant for all of them, as "some positive constant that depends on
whether we employ the weak or strong notion of typicality" says; we use weak typicality. (15.18)
carries no quantifier on `n` in the book and is stated for every `n`; (15.19) for `n ≥ N`.
`Tr{Π}` is the real part of the trace (the dimension of the typical subspace). `H(A)` is the
published `QAlgorithms.vnEntropy ρ` (bits). -/
theorem property_15_1_2 :
    ∃ c : ℝ, 0 < c ∧ ∀ {a : Type} [Fintype a] [DecidableEq a] (ρ U : Matrix a a ℂ)
      (p : FinDist a), IsSpectralDecomposition ρ U p → ∀ δ : ℝ, 0 < δ →
        (∀ n : ℕ, (typicalProjector U p n δ).trace.re ≤
          (2 : ℝ) ^ ((n : ℝ) * (QAlgorithms.vnEntropy ρ + c * δ))) ∧
        ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ N : ℕ, ∀ n ≥ N,
          (1 - ε) * (2 : ℝ) ^ ((n : ℝ) * (QAlgorithms.vnEntropy ρ - c * δ)) ≤
            (typicalProjector U p n δ).trace.re := by sorry

end WildeQIT.Schumacher
