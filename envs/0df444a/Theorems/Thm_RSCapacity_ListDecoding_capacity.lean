-- Prove2me | Theorems.Thm_RSCapacity_ListDecoding_capacity
-- name    : RSCapacity.ListDecoding.capacity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:58:47.897041+00:00
-- url     : https://prove2.me/theorems/95547cb3-7701-4027-8563-9aa3f8075728
-- title:
--   Theorem 1.1 — algorithmic list-decoding up to capacity
-- statement:
--   There is one deterministic finite binary decoder. For every finite field $F$ of size $q$ and characteristic $p$, every field labelling, positive integers $k,n$ with $p>k$, any distinct evaluation points $\alpha_1,\ldots,\alpha_n$ and arbitrary received word $y\in F^n$, it terminates with exactly
--   $$\mathcal L_{k,A}(\alpha,y)=\{f\in F[X]:\deg f<k,\ |\{i:f(\alpha_i)=y_i\}|\ge A\}$$
--   for every supplied integer $0\le A\le n+1$. Moreover, for every positive real $\varepsilon,\rho$ there exist a positive exponent $C=C(\varepsilon,\rho)$ and integer $N\ge1$, chosen before the field and all instance data, such that if $k,n\ge N$ and $k/n\ge\rho$, the actual worst-case running time is at most
--   $$q^C\qquad\text{whenever}\quad A\ge k(1+\varepsilon)\ \text{or}\ A=n+1.$$
--   The source's exact output and time bound are obtained by supplying $A=\min\{n+1,\lceil k(1+\varepsilon)\rceil\}$. Thus every real $\varepsilon>0$, every positive rate lower bound, every extension field, and all source instances are retained. Injectivity implies $q\ge n$; no $k\le n$ restriction is added. If the threshold exceeds $n$, the exact output is empty. Degree is strictly less than $k$, including zero, and output comprises distinct polynomial coefficient vectors, rather than merely distinct evaluation vectors.
--
--   The program reads the public operation tables and numerical and vector input. The step bound includes parsing, arithmetic, interpolation, differential-equation enumeration, filtering and output. No interpolation existence, decoder correctness or cost certificate is a hypothesis. This is the full algorithmic capacity target, with research proofs left open.
--
--   Differences from the source:
--   - reading: the finite representation of real ε in the algorithm input is unspecified, while p.1 supplies an agreement parameter A → a supplied capped integer cutoff represents the exact output effect of ε; arbitrary positive real ε remains in the specification; reason: agreement is an integer at most n, so the capped ceiling recovers exactly every source output without an exact-real oracle
--   - generalization: a capacity decoder for each parameter regime → one finite program is correct for every integer A in [0,n+1], with a uniform q^C bound for A≥k(1+ε) or A=n+1; reason: specialize to the capped ceiling; the cap branch gives the empty result for all otherwise unattainable thresholds
--   - encoding: arbitrary finite fields, distinct points, polynomial output and polynomial runtime → all field-table labellings, Fin n indices, degree in WithBot ℕ, padded k-coefficient lists without duplicates, and actual binary instructions; reason: every finite field has a labelling and prime-power size, injectivity supplies q≥n, zero has degree minus infinity, and polynomial-size table and output costs are included; C and N precede all data
-- source:
--   Prahladh Harsha, Mrinal Kumar, Ramprasad Saptharishi, STOC 2027 submission #495 (October 2026), Theorem 1.1, p.2; agreement-input convention p.1; Algorithm 1, p.17; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/495.pdf

import Mathlib
import Definitions.Def_RSCapacity_ListDecoding_Evaluation

namespace RSCapacity.ListDecoding

/-- Theorem 1.1, submission #495 p.2, with the p.1 integer agreement
interface. The same executable works for all integer thresholds; real epsilon
remains universally quantified in the complexity specification. -/
theorem capacity :
    ∃ decoder : Program, FuzzyExtractors.ImprovedJSFull.Deterministic decoder ∧
      (∀ (F : Type) [Field F] [Fintype F] (P : FieldPresentation F)
        (k n A : ℕ) (α y : Fin n → F),
        0 < k → 0 < n → k < ringChar F → A ≤ n + 1 → Function.Injective α →
        Executes decoder (decoderInput P k n A α y)
          (polynomialOutput P k (decodingTarget k A α y))) ∧
      ∀ ε ρ : ℝ, 0 < ε → 0 < ρ →
        ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 0 < N ∧
        ∀ (F : Type) [Field F] [Fintype F] (P : FieldPresentation F)
          (k n A : ℕ) (α y : Fin n → F),
          N ≤ k → N ≤ n → k < ringChar F → ρ ≤ (k : ℝ) / n →
          A ≤ n + 1 → ((k : ℝ) * (1 + ε) ≤ A ∨ A = n + 1) →
          Function.Injective α →
          ExecutesWithin decoder (decoderInput P k n A α y)
            (((Fintype.card F : ℕ) : ℝ) ^ C)
            (polynomialOutput P k (decodingTarget k A α y)) := by sorry

end RSCapacity.ListDecoding
