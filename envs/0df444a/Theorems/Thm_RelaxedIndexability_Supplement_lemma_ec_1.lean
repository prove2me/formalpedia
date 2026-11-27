-- Prove2me | Theorems.Thm_RelaxedIndexability_Supplement_lemma_ec_1
-- name    : RelaxedIndexability.Supplement.lemma_ec_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T03:05:31.444429+00:00
-- url     : https://prove2.me/theorems/c77ebc97-3628-562e-916f-a4bac778c69c
-- title:
--   Lemma EC.1 — for three states the $k$-step reward has one of three closed forms
-- statement:
--   Let $\mathbf P$ be an irreducible and aperiodic $3\times3$ transition matrix, $B\in\mathbb R^3$ a reward vector, $\omega$ a belief, and $h(k)=\omega\mathbf P^kB'$ the $k$-step reward function. Then:
--
--   1. if $\mathbf P$ has only real eigenvalues and 3 linearly independent eigenvectors, $h(k)=a_1b_1^k+a_2b_2^k+c$ for some $a_1,b_1,a_2,b_2,c\in\mathbb R$ with $|b_1|,|b_2|<1$;
--   2. if $\mathbf P$ has only real eigenvalues and exactly 2 linearly independent eigenvectors, $h(k)=ab^k+ckb^{k-1}+d$ for some $a,b,c,d\in\mathbb R$ with $|b|<1$;
--   3. if $\mathbf P$ has a pair of conjugate complex eigenvalues, $h(k)=a'A^k\sin(k\theta+b')+c'$ for some real $a',A,b',c',\theta$ with $A\in(0,1)$, $a'\ge0$, $\theta\in(0,2\pi)$, $b'\in[0,2\pi)$;
--
--   and one of the three hypotheses holds.
--
--   These forms are the input of Theorem EC.1, which computes the first crossing time of the threshold policy for three-state arms.
--
--   **Formalization Note** "Irreducible and aperiodic" is `Matrix.IsPrimitive`, some power of $\mathbf P$ being entrywise positive, as on p.ec11. Eigenvalues are the complex roots of the characteristic polynomial. The number of linearly independent eigenvectors is the dimension of the span of the real eigenvectors.
--
--   Differences from the source:
--   - encoding: P irreducible and aperiodic → Matrix.IsPrimitive P; reason: for a finite stochastic matrix the two are equivalent (the paper's "regular", p.ec11)
--   - encoding: "2 linearly independent eigenvectors" → the real eigenvectors span a space of dimension exactly 2; reason: the case of the Jordan form (EC.44) has exactly two, and the dimension of the span is the maximal number of independent eigenvectors
--   - generalization: 0 = B₀ ≤ ⋯ ≤ B_{K−1} (p.11) → not assumed; reason: the lemma does not use it; every B includes the source's case
-- source:
--   Liu, Relaxed Indexability and Index Policy for Partially Observable Restless Bandits, arXiv:2107.11939v4, Lemma EC.1, pp.ec12–ec13 (§EC.7, p.ec10)

import Mathlib
import Definitions.Def_RelaxedIndexability_Supplement_kStepReward

open Matrix

namespace RelaxedIndexability.Supplement

/-- **Lemma EC.1** (Liu, arXiv:2107.11939v4, Lemma EC.1, pp.ec12–ec13). Let `P` be an irreducible
and aperiodic `3 × 3` transition matrix (§EC.7), `B` a reward vector and `ω` a belief.

1. If `P` has only real eigenvalues and 3 linearly independent eigenvectors, then
   `h(k) = a₁ b₁^k + a₂ b₂^k + c` with `|b₁|, |b₂| < 1`.
2. If `P` has only real eigenvalues and exactly 2 linearly independent eigenvectors, then
   `h(k) = a b^k + c k b^(k−1) + d` with `|b| < 1`.
3. If `P` has a pair of conjugate complex (non-real) eigenvalues, then
   `h(k) = a′ A^k sin(kθ + b′) + c′` with `A ∈ (0,1)`, `a′ ≥ 0`, `θ ∈ (0, 2π)`, `b′ ∈ [0, 2π)`.

One of the three hypotheses holds.

**Formalization Note.** Irreducible and aperiodic is the equivalent `Matrix.IsPrimitive` (some
power of `P` is entrywise positive, as on p.ec11). Eigenvalues are the complex roots of the
characteristic polynomial. The number of linearly independent eigenvectors is the dimension of the
real span of the real eigenvectors, which are all of them when the eigenvalues are real. A real
matrix with a non-real eigenvalue also has its conjugate as an eigenvalue. -/
theorem lemma_ec_1 (P : Matrix (Fin 3) (Fin 3) ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ (Fin 3)) (hprim : P.IsPrimitive)
    (B : Fin 3 → ℝ) (ω : Fin 3 → ℝ) (hω : ω ∈ stdSimplex ℝ (Fin 3)) :
    ((∀ z : ℂ, (P.map (fun x : ℝ => (x : ℂ))).charpoly.IsRoot z → z.im = 0) →
      Module.finrank ℝ (Submodule.span ℝ {v : Fin 3 → ℝ | ∃ μ : ℝ, P *ᵥ v = μ • v}) = 3 →
      ∃ a₁ b₁ a₂ b₂ c : ℝ, IsDiagonalizableForm (kStepReward P B ω) a₁ b₁ a₂ b₂ c) ∧
    ((∀ z : ℂ, (P.map (fun x : ℝ => (x : ℂ))).charpoly.IsRoot z → z.im = 0) →
      Module.finrank ℝ (Submodule.span ℝ {v : Fin 3 → ℝ | ∃ μ : ℝ, P *ᵥ v = μ • v}) = 2 →
      ∃ a b c d : ℝ, IsJordanForm (kStepReward P B ω) a b c d) ∧
    ((∃ z : ℂ, (P.map (fun x : ℝ => (x : ℂ))).charpoly.IsRoot z ∧ z.im ≠ 0) →
      ∃ a' A θ b' c' : ℝ, IsComplexForm (kStepReward P B ω) a' A θ b' c') ∧
    (((∀ z : ℂ, (P.map (fun x : ℝ => (x : ℂ))).charpoly.IsRoot z → z.im = 0) ∧
        (Module.finrank ℝ (Submodule.span ℝ {v : Fin 3 → ℝ | ∃ μ : ℝ, P *ᵥ v = μ • v}) = 3 ∨
          Module.finrank ℝ (Submodule.span ℝ {v : Fin 3 → ℝ | ∃ μ : ℝ, P *ᵥ v = μ • v}) = 2)) ∨
      ∃ z : ℂ, (P.map (fun x : ℝ => (x : ℂ))).charpoly.IsRoot z ∧ z.im ≠ 0) := by sorry

end RelaxedIndexability.Supplement
