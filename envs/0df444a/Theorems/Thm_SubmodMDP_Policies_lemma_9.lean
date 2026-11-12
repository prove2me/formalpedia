-- Prove2me | Theorems.Thm_SubmodMDP_Policies_lemma_9
-- name    : SubmodMDP.Policies.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:11:23.171192+00:00
-- url     : https://prove2.me/theorems/58c21041-e326-40ae-b938-2212767fd465
-- title:
--   Lemma 9 — rounding a linear cut to small integer coefficients
-- statement:
--   Let $\varepsilon>0$, $n=|V|\ge1$, $c_D$ a positive integer (in the paper, the one of Lemma 8), $f:2^V\to\mathbb Q_{\ge0}$ monotone submodular, $\ell(y)=\sum_{|I|\le r+1}\ell_Iy_I$ with $\ell_I\in[0,f(V)]$, and
--   $$T\in\Big[\frac{f(V)}{n\,c_D},\ f(V)\Big].$$
--   One can compute in time $n^{O(r)}$ another linear function $\bar\ell(y)=\sum_{|I|\le r+1}\bar\ell_Iy_I$ and $\bar T\in\mathbb Z_{\ge0}$ such that all coefficients $\bar\ell_I$ and $\bar T$ are non-negative integers bounded by $2c_D^2n^{r+3}/\varepsilon+1$, and for all $y\in[0,1]^{\binom{V}{\le r+1}}$:
--
--   1. $\bar\ell(y)<\bar T\ \Rightarrow\ \ell(y)<T$;
--   2. $\ell(y)<(1-\varepsilon)T\ \Rightarrow\ \bar\ell(y)<\bar T$.
--
--   The rounded cuts have bit length independent of the values of $f$, which keeps the ellipsoid method of Lemma 7 polynomial in $n^r$ and $\langle D,b\rangle$.
--
--   Differences from the source:
--   - encoding: time n^{O(r)} (ε fixed in the context of Lemma 7) → ∀ ε > 0, ∃ c and a deterministic program, every run halts within (n+1)^{c(r+1)}; reason: instantiation of O(·); the constant comes after ε as in the source's quantifier order
--   - generalization: c_D as in Lemma 8 → any positive integer c_D; reason: the statement and the proof use only that c_D is a positive integer; it specializes to the c_D of Lemma 8
--   - encoding: n = |V| (a layered graph with Q^(r) ∩ {Dy ≤ b} ≠ ∅, so n ≥ H ≥ 1) → hypothesis 1 ≤ n; reason: nondegeneracy only: with n = 0 the interval [f(V)/(n c_D), f(V)] is undefined (Lean's division by zero would turn it into [0, f(∅)], which admits a false instance)
--   - reading: running time as the number of word-RAM operations, words large enough to store every input value and every value of f (footnote 2); no fixed instruction set or randomness primitive → the randomized value-oracle integer RAM of SubmodMDP.Policies.Machine: integer registers, +, -, ×, floor division/modulus, indirect addressing, jumps, a value-oracle query and rand M (uniform on {0,…,M-1}); an instruction on operands of k words of w bits costs (1+k)², a query on m indices (1+m)(1+k)², w covers ⌈log₂(input length+2)⌉, every input integer and every numerator/denominator of f; every run must halt within the bound; reason: footnote 2 fixes only the word size; every instruction is simulable on a w-bit word RAM in O(cost) operations, so a bound here implies the paper's; exact sampling (rand M) is needed because with fair coins only, an exact law with probabilities 1/3 cannot be produced within a worst-case bound, which would falsify the exact distributional claims
--   - reading: f : 2^V → ℝ≥0 monotone submodular, given by a value oracle → f : Finset V → ℚ with 0 ≤ f, monotone and submodular after the cast to ℝ, accessed only through the machine's query instruction; reason: footnote 2 requires every value of f to fit in a word, which forces a finite representation
--   - encoding: ℓ_I and T real; outputs ℓ̄, T̄ → ℓ_I and T rational inputs; outputs decoded from a fixed format (the ℓ̄_I in order, then T̄); reason: inputs of an algorithm are finitely represented; ℓ comes from Lemma 5, whose coefficients are rational
-- source:
--   Lars Rohwedder, Rico Zenklusen, STOC 2027 submission #658 (October 2026), Lemma 9, p. 15 (PDF p. 16)

import Mathlib
import Definitions.Def_SubmodMDP_Policies_Layered
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_SubsamplingSM_Offline_IsMonotoneSetFn

namespace SubmodMDP.Policies

open NonmonotoneSubmod.Shared SubsamplingSM.Offline

/-- Lemma 9 (PDF p. 15), with `n^{O(r)}` instantiated as `(n+1)^{c(r+1)}` (`c` may depend on the
fixed `ε`), `n = |V|`, for every positive integer `c_D`. Given a linear function `ℓ` with
`ℓ_I ∈ [0, f(V)]` and `T ∈ [f(V)/(n c_D), f(V)]`, a deterministic program computes non-negative
integers `ℓ̄_I`, `T̄`, all at most `2 c_D² n^{r+3}/ε + 1`, such that for all `y ∈ [0,1]^{(V choose ≤r+1)}`:
`ℓ̄(y) < T̄ ⇒ ℓ(y) < T`, and `ℓ(y) < (1-ε)T ⇒ ℓ̄(y) < T̄`. -/
theorem lemma_9 (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℕ, ∃ Alg : Program, Alg.Deterministic ∧
    ∀ N : ℕ, 1 ≤ N → ∀ r cD : ℕ, 1 ≤ cD →
    ∀ f : Finset (Fin N) → ℚ, (∀ X, 0 ≤ f X) → IsMonotoneSetFn (fun X => (f X : ℝ)) →
      Submodular (fun X => (f X : ℝ)) →
    ∀ ℓ : Finset (Fin N) → ℚ, (∀ I : Finset (Fin N), I.card ≤ r + 1 → 0 ≤ ℓ I ∧ ℓ I ≤ f Finset.univ) →
    ∀ T : ℚ, f Finset.univ / ((N : ℚ) * (cD : ℚ)) ≤ T → T ≤ f Finset.univ →
    let O : Oracle := ⟨N, f⟩
    let inp : List ℤ := [(N : ℤ), (r : ℤ), (cD : ℤ)] ++ encPoint N (r + 1) ℓ ++ encRat T
    let B : ℕ := (N + 1) ^ (c * (r + 1))
    HaltsWithin Alg O (wordLen inp O) inp B ∧
    ∀ σ : List ℤ, some σ ∈ (outLaw Alg O (wordLen inp O) inp B).support →
      ∃ ℓb : Finset (Fin N) → ℕ, ∃ Tb : ℕ, decodeL9 N r σ = some (ℓb, Tb) ∧
        (∀ I : Finset (Fin N), I.card ≤ r + 1 →
          (ℓb I : ℝ) ≤ 2 * (cD : ℝ) ^ 2 * (N : ℝ) ^ (r + 3) / ε + 1) ∧
        (Tb : ℝ) ≤ 2 * (cD : ℝ) ^ 2 * (N : ℝ) ^ (r + 3) / ε + 1 ∧
        ∀ y : Finset (Fin N) → ℝ, (∀ I : Finset (Fin N), I.card ≤ r + 1 → 0 ≤ y I ∧ y I ≤ 1) →
          (linEval r (fun I => (ℓb I : ℝ)) y < (Tb : ℝ) →
              linEval r (fun I => (ℓ I : ℝ)) y < (T : ℝ)) ∧
          (linEval r (fun I => (ℓ I : ℝ)) y < (1 - ε) * (T : ℝ) →
              linEval r (fun I => (ℓb I : ℝ)) y < (Tb : ℝ)) := by sorry

end SubmodMDP.Policies
