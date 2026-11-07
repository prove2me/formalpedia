-- Prove2me | Theorems.Thm_SubexpPrimes_lemma_3_1_convolution
-- name    : SubexpPrimes.lemma_3_1_convolution
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:58:32.101511+00:00
-- url     : https://prove2.me/theorems/5a85a24c-2003-4b70-9630-796f706f2b1d
-- title:
--   Lemma 3.1 — convolution: $O(Kw)$ edges and degree at most $2\sqrt{\varrho K}\,w$
-- statement:
--   Let $R$ be a commutative ring with an injective $w$-bit encoding, and let $K=\varrho^r\ge2$ with $\varrho\in\{2,3\}$, where $K$ is a unit in $R$. Let $\omega\in R$ be a principal $K$-th root of unity, that is, $\omega^K=1$ and $\sum_{i<K}\omega^{ij}=0$ for $0<j<K$. Then the relation $c=a\star b$ on $a,b,c\in R^K$, where
--
--   $$
--   (a\star b)_t=\sum_{i+i'\equiv t\ (\mathrm{mod}\ K)}a_ib_{i'},
--   $$
--
--   has a functional representation with $O(Kw)$ edges and degree at most $2\sqrt{\varrho K}\,w$. The constant in $O(Kw)$ is absolute. Words that are not encodings are rejected.
--
--   This is what makes linear-size multiplication possible: a vertex may run any computation on its own bits, so only a few intermediate results of the Fourier transform need to be exposed.
--
--   Differences from the source:
--   - generalization: elements with w-bit encodings, with polynomial-time ring operations → any injective w-bit encoding, with no assumption on the cost of the ring operations and no machine clause; reason: R is abstract, so a machine clause has no meaning; the existence holds for all encodings, including those of the source
--   - encoding: the relation on a, b, c ∈ R^K → a predicate on one word of 3Kw bits, the concatenated encodings; reason: a word of this form stands for exactly one triple
-- source:
--   Gajulapalli, Deterministic Construction of Primes in Subexponential Time (manuscript, sha256 6ad4d3de…), Lemma 3.1, p.17

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_SubexpPrimes_NetDesc
import Definitions.Def_SubexpPrimes_IsFunctionalRep

set_option autoImplicit false

namespace SubexpPrimes

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- **Lemma 3.1 (Convolution)** — Gajulapalli, *Deterministic Construction of Primes in Subexponential Time*
(manuscript, sha256 6ad4d3de…), p.17.

For a commutative ring `R` with an injective `w`-bit encoding, `K = ϱ^r ≥ 2` with `ϱ ∈ {2, 3}`, `K`
a unit in `R` and `ω` a principal `K`-th root of unity (`ω^K = 1` and `∑_{i<K} ω^{ij} = 0` for
`0 < j < K`), the relation `c = a ⋆ b` on `a, b, c ∈ R^K`, where
`(a ⋆ b)_t = ∑_{i+i' ≡ t (mod K)} a_i b_{i'}`, has a functional representation with `O(Kw)` edges and
degree at most `2√(ϱK) w`. A word that is not the encoding of three vectors is rejected.

**Formalization Note.** `C₀` is absolute, fixed before `R`. The factor `2` in the degree is printed.
The lemma has no machine clause, because `R` is abstract, so the hypothesis of polynomial-time ring
operations has no role here and is not stated. The uniform versions are in Corollary 3.2. -/
theorem lemma_3_1_convolution :
    ∃ C₀ : ℕ, ∀ (R : Type) [CommRing R] (w : ℕ) (enc : R → List Bool),
      Function.Injective enc → (∀ x, (enc x).length = w) →
      ∀ (ϱ r K : ℕ), (ϱ = 2 ∨ ϱ = 3) → K = ϱ ^ r → 2 ≤ K → IsUnit (K : R) →
      ∀ ω : R, ω ^ K = 1 → (∀ j, 0 < j → j < K → ∑ i ∈ Finset.range K, ω ^ (i * j) = 0) →
      ∃ (D : NetDesc) (T : D.Tables ℚ),
        D.inputs.length = 3 * K * w ∧
        D.m ≤ C₀ * K * w ∧
        (D.maxDeg : ℝ) ≤ 2 * Real.sqrt ((ϱ : ℝ) * K) * w ∧
        IsFunctionalRep (D.net T) D.inputs (fun x =>
          ∃ a b c : Fin K → R,
            x = (List.ofFn a).flatMap enc ++ (List.ofFn b).flatMap enc ++ (List.ofFn c).flatMap enc ∧
            ∀ t : Fin K, c t =
              ∑ i : Fin K, ∑ i' : Fin K, if (i.val + i'.val) % K = t.val then a i * b i' else 0) := by sorry

end SubexpPrimes
