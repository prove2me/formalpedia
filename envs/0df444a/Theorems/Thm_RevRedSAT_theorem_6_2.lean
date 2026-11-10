-- Prove2me | Theorems.Thm_RevRedSAT_theorem_6_2
-- name    : RevRedSAT.theorem_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:47:43.8498+00:00
-- url     : https://prove2.me/theorems/2820df6e-0cb9-41bb-a757-0b8aba53add9
-- title:
--   Theorem 6.2 — solution-preserving sparsification into at most $2^{\delta k}$ families
-- statement:
--   Fix $d\ge2$. There are an algorithm and constants $C,e$ such that, given a rank-$d$ instance $(U,\mathcal F,k)$ with code $w$ and $\delta=2^{-j}$ for an integer $j\ge2$, it outputs at most $2^{\delta k}$ families (repetitions counted) within $\lfloor 2^{\delta k}\,C\,(|w|+j+1)^e\rfloor$ steps, such that:
--
--   1. each family has rank at most $d$ and frequency at most $T_d(\delta)=1+\sum_{p=1}^{d-1}(2d/\delta)^{4p}/(4d)$;
--   2. every hitting set $X$ of $\mathcal F$ with $|X|\le k$ hits at least one returned family, and every hitting set of any returned family, of any size, hits $\mathcal F$;
--   3. every set of a returned family is contained in a set of $\mathcal F$.
--
--   The budget is not changed, which is what later allows a compact encoding of the selected elements.
--
--   **Formalization Note** $\mathrm{poly}_d(|I|,\mathrm{bits}(\delta))$ is $C(|w|+j+1)^e$; the bound $T_d(\delta)=O_d(\delta^{-(4d-4)})$ is clause 2 of Lemma B.8.
--
--   Differences from the source:
--   - encoding: an algorithm whose running time counts bit operations (no machine model named) → a Mathlib TM2 machine with finite stack alphabets, time = number of steps; reason: polynomial changes of model are absorbed by the polynomial factor and the 2^{o(·)}, 2^{O(·)} classes
--   - encoding: the explicit binary encoding of the input → fixed self-delimiting codes; every listing order of the input is an admissible code; reason: the codes are injective and of polynomial length; quantifying over all codes adds no precomputed information
--   - reading: bits(δ) for δ = 2^{−j} → j + 1; reason: the binary length of the denominator 2^j; the binary length of j itself would only shorten the bound
--   - encoding: poly_d(|I|, bits(δ)) → C·(|w| + j + 1)^e with C, e chosen after d; reason: a polynomial in the two lengths with d-dependent constants
-- source:
--   Kundu, Panolan, Saurabh, Xue, Zehavi, Reverse Reductions: From Faster SAT to Subexponential Algorithms, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Theorem 6.2, p.39 (printed) = PDF p.41

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_RevRedSAT_FiniteAlphabets
import Definitions.Def_RevRedSAT_IsHSCode
import Definitions.Def_RevRedSAT_frequency
import Definitions.Def_RevRedSAT_mu

set_option autoImplicit false

namespace RevRedSAT

open RSListDecodingCapacity.AllRates

/-- **Theorem 6.2 (solution-preserving sparsification).**
Kundu, Panolan, Saurabh, Xue, Zehavi, *Reverse Reductions: From Faster SAT to Subexponential
Algorithms*, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Theorem 6.2, p.39: "Fix d ≥ 2. Given a rank-d set family F ⊆ 2^U, a budget k ≥ 0, and δ = 2^{−j}
for an integer j ≥ 2, one can construct at most 2^{δk} leaf occurrences in time
2^{δk} poly_d(|I|, bits(δ)). The returned families have the following properties: 1. Each family has
rank at most d and frequency at most T_d(δ) := 1 + Σ_{p=1}^{d−1} (2d/δ)^{4p}/(4d) = O_d(δ^{−(4d−4)}).
2. Every hitting set X ⊆ U of F with |X| ≤ k hits at least one returned family. Conversely, every
hitting set of any returned family, regardless of its cardinality, hits F. 3. Every set in a
returned family is contained in an original input set."

For every `d ≥ 2` there are a finite-alphabet machine and constants `C, e` such that on every code
`w` of a rank-`d` instance `(U, F, k)` followed by `j ≥ 2` (`δ = 2^{−j}`), the machine outputs within
`⌊2^{δk}·C·(|w| + j + 1)^e⌋` steps the code of a list of at most `2^{δk}` families (repetitions
counted) such that: each has rank at most `d` and frequency at most `T_d(δ)`; every hitting set of
`F` of size at most `k` hits some listed family; every hitting set of a listed family hits `F`; and
every set of a listed family is contained in a set of `F`.

**Formalization Note** `bits(δ)` for `δ = 2^{−j}` is taken as `j + 1` (the binary length of the
denominator `2^j`). The `O_d(δ^{−(4d−4)})` estimate of `T_d(δ)` is clause 2 of `lemma_B_8`. Leaves
are listed with repetitions ("each leaf is counted separately", p.39). -/
theorem theorem_6_2 :
    ∀ d : ℕ, 2 ≤ d →
      ∃ M : Turing.TM2ComputableAux Bool Bool, FiniteAlphabets M ∧ ∃ (C : ℝ) (e : ℕ),
        ∀ (I : HSElemKernel.HSInstance) (w : List Bool) (j : ℕ), IsDHSCode d I w → 2 ≤ j →
          ∃ (Fs : List (Finset (Finset (Fin I.n)))) (out : List Bool),
            IsFamListCode Fs out ∧
            HMBinPacking.OutputsWithin M (w ++ encNat j) out
              ⌊(2 : ℝ) ^ (deltaOf j * I.k) * C * ((w.length : ℝ) + j + 1) ^ e⌋₊ ∧
            (Fs.length : ℝ) ≤ (2 : ℝ) ^ (deltaOf j * I.k) ∧
            (∀ G ∈ Fs, (∀ S ∈ G, S.card ≤ d) ∧ (frequency G : ℝ) ≤ Td d j) ∧
            (∀ X : Finset (Fin I.n), AlgebraicFPT.HittingSet.IsHitting I.S X → X.card ≤ I.k →
              ∃ G ∈ Fs, AlgebraicFPT.HittingSet.IsHitting G X) ∧
            (∀ G ∈ Fs, ∀ X : Finset (Fin I.n), AlgebraicFPT.HittingSet.IsHitting G X →
              AlgebraicFPT.HittingSet.IsHitting I.S X) ∧
            (∀ G ∈ Fs, ∀ S ∈ G, ∃ T ∈ I.S, S ⊆ T) := by sorry

end RevRedSAT
