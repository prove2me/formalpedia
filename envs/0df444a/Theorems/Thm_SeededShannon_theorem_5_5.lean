-- Prove2me | Theorems.Thm_SeededShannon_theorem_5_5
-- name    : SeededShannon.theorem_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:46:53.175167+00:00
-- url     : https://prove2.me/theorems/ba3b225e-3ea9-4a78-8e37-94ed42a39329
-- title:
--   Theorem 5.5 — sparse set agreement embedding
-- statement:
--   For every constant $0<p<1$ there are a polynomial $N_{\min}$, a constant $\gamma>0$, efficiently computable, polynomially bounded integer functions $B(\lambda,n)$, $L(\lambda,n)$ with $B=O(n^{1-\gamma})$, and a recoverable embedding (Definition 5.4) with minimum input length $N_{\min}$ for the family
--   $$\mathcal F_{\lambda,n}=\{f_S:S\subseteq[n],\ |S|\le B(\lambda,n)\},\qquad f_S(x)=1\iff\delta(x)\le p\wedge x_S=1,$$
--   such that
--
--   1. the parameters are always perfectly recoverable;
--   2. each sampled $f_S$ is described by $S$;
--   3. recovery outputs at most $L(\lambda,n)$ seeds;
--   4. every sampled $f_S$ accepts the indicator vector of $S$.
--
--   With Theorem A.1 it gives the sparse-set obfuscator of Theorem 5.2.
--
--   **Formalization Note** Sets are indicator vectors. "Described by $S$": a polynomial-time map reads the indicator of $S$ off the sampled description, and the description evaluates to $f_S$.
--
--   Differences from the source:
--   - encoding: f_S is described by S → a polynomial-time map from the sampled description to the indicator vector of S, and the description evaluates to f_S; reason: a description determines S efficiently and computes f_S
--   - encoding: B = O(n^{1−γ}) → B(λ, n) ≤ C · n^{1−γ} for one constant C, all λ and all n ≥ N_min(λ); reason: the family is defined for n ≥ N_min(λ); the constant is uniform in λ as printed
--   - encoding: parameters always perfectly recoverable → for every coin string of SampleParams; reason: the support of SampleParams is the set of outputs over all coins
--   - encoding: for every polynomially bounded n (every polynomial P) → pointwise clauses for all n ≥ N_min(λ); probabilistic clauses for every bound n ≤ (λ+2)^c; reason: the pointwise clauses hold at each length, and every polynomial is bounded by some (λ+2)^c
-- source:
--   Dujmovic, Lu, Silbak, Wichs, Shannon Rate Seeded Codes from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 52f4b606…a769709), Theorem 5.5, p.32 (PDF p.35)

import Mathlib
import Definitions.Def_SeededShannon_RecEmb
import Definitions.Def_SeededShannon_setFamily
import Definitions.Def_SeededShannon_SeededCode

set_option autoImplicit false

namespace SeededShannon

open LaconicBarrier NoisyOWMPC

/-- **Theorem 5.5 (Sparse Set Agreement Embedding)** (Dujmovic, Lu, Silbak, Wichs, STOC 2027
submission (manuscript sha256 52f4b606…a769709), Theorem 5.5, p.32): for every constant `0 < p < 1`
there are a polynomial `N_min`, a constant `γ > 0` and efficiently computable, polynomially bounded
integer-valued `B(λ, n)`, `L(λ, n)` with `B = O(n^{1−γ})`, and a recoverable embedding with minimum
input length `N_min` for the family `F_{λ,n} = {f_S : S ⊆ [n], |S| ≤ B(λ, n)}`,
`f_S(x) = 1 ⟺ δ(x) ≤ p ∧ x_S = 1`, whose parameters are always perfectly recoverable. `f_S` is
described by `S`, recovery outputs at most `L(λ, n)` seeds, and every sampled `f_S` accepts the
indicator vector of `S`.

**Formalization Note** Sets `S ⊆ [n]` are indicator vectors. "`f_S` is described by `S`" is: a
polynomial-time map `setOf` reads the indicator vector of `S` off the sampled description, and the
description evaluates to `f_S`. `B = O(n^{1−γ})` is `B(λ, n) ≤ C · n^{1−γ}` for one constant `C`,
all `λ` and all `n ≥ N_min(λ)`. "Always" is every coin string of `SampleParams`. -/
theorem theorem_5_5 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ (Nmin : ℕ → ℕ) (γ : ℝ) (B L : ℕ → ℕ → ℕ), PolyParam Nmin ∧ 0 < γ ∧
      EffComputable₂ B ∧ EffComputable₂ L ∧ PolyBounded₂ B ∧ PolyBounded₂ L ∧
      (∃ C : ℝ, ∀ lam n, Nmin lam ≤ n → (B lam n : ℝ) ≤ C * (n : ℝ) ^ (1 - γ)) ∧
      ∃ (E : RecEmb) (setOf : ℕ → ℕ → List Bool → List Bool),
        E.IsRecEmb Nmin (fun _ _ => True) (setFamily p B) ∧
        (∀ lam n, Nmin lam ≤ n → ∀ r : Fin (E.ppCoins lam n) → Bool,
          E.PerfectlyRecoverable lam n (E.sampleParams lam n r)) ∧
        (∀ lam n, Nmin lam ≤ n → ∀ (r : Fin (E.ppCoins lam n) → Bool) (y : Fin n → Bool),
          (E.recoverSeeds (E.sampleParams lam n r) (bits y)).length ≤ L lam n) ∧
        PolyTimeOn (ι := (z : {z : ℕ × ℕ // Nmin z.1 ≤ z.2}) ×
            (Fin (E.ppCoins z.1.1 z.1.2) → Bool) × (Fin z.1.1 → Bool))
          (fun i => [unary i.1.1.1, unary i.1.1.2,
            E.sampleFunc (E.sampleParams i.1.1.1 i.1.1.2 i.2.1) (bits i.2.2)])
          (fun i => setOf i.1.1.1 i.1.1.2
            (E.sampleFunc (E.sampleParams i.1.1.1 i.1.1.2 i.2.1) (bits i.2.2))) ∧
        ∀ lam n, Nmin lam ≤ n → ∀ (r : Fin (E.ppCoins lam n) → Bool) (u : Fin lam → Bool),
          ∃ S : Fin n → Bool,
            setOf lam n (E.sampleFunc (E.sampleParams lam n r) (bits u)) = bits S ∧
            wt S ≤ B lam n ∧
            (∀ y : Fin n → Bool,
              E.evalDesc (E.sampleFunc (E.sampleParams lam n r) (bits u)) (bits y) = true ↔
                setAgree p S y) ∧
            E.evalDesc (E.sampleFunc (E.sampleParams lam n r) (bits u)) (bits S) = true := by sorry

end SeededShannon
