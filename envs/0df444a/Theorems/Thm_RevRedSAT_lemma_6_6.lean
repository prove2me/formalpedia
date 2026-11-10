-- Prove2me | Theorems.Thm_RevRedSAT_lemma_6_6
-- name    : RevRedSAT.lemma_6_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:47:57.314773+00:00
-- url     : https://prove2.me/theorems/de5d2ac3-2f85-434c-87d3-0c3703b2b510
-- title:
--   Lemma 6.6 — a polynomial element kernel keeping the budget k, with solution lifting
-- statement:
--   There are a computable function $f$ and an absolute exponent $c$ such that for every fixed $d\ge2$ the following holds. A $d$-Hitting Set instance $I=(U,\mathcal F,k)$ with $k\ge1$ can be reduced deterministically to an equivalent rank-$d$ instance $I'=(U',\mathcal F',k)$ with the same budget and
--
--   $$|U'|=O_d(k^{d-1}),\qquad |\mathcal F'|=O_d(k^d),$$
--
--   in $f(d)|I|^{c}+k^{O_d(1)}$ steps; and a solution of $I'$ can be converted in polynomial time into a solution of $I$ of size at most $k$.
--
--   The lemma is the element kernel of Abu-Khzam in the form of van Bevern, cited by the paper; it makes all later list constructions and SAT encodings polynomial in $k$.
--
--   **Formalization Note** The lifting is a second machine whose input is the original code, the reduced code and the listed reduced solution.
--
--   Differences from the source:
--   - encoding: an algorithm whose running time counts bit operations (no machine model named) → a Mathlib TM2 machine with finite stack alphabets, time = number of steps; reason: polynomial changes of model are absorbed by the polynomial factor and the 2^{o(·)}, 2^{O(·)} classes
--   - encoding: the explicit binary encoding of the input → fixed self-delimiting codes; every listing order of the input is an admissible code; reason: the codes are injective and of polynomial length; quantifying over all codes adds no precomputed information
--   - encoding: O_d(·) bounds and k^{O_d(1)} → constants C, e chosen after d and before the instance; reason: the meaning of O_d
--   - encoding: a solution of the reduced instance can be converted in polynomial time → a lifting machine on input (original code, reduced code, listed solution) within C·(input length + 1)^e steps; reason: the conversion needs both instances; the degree may depend on d
-- source:
--   Kundu, Panolan, Saurabh, Xue, Zehavi, Reverse Reductions: From Faster SAT to Subexponential Algorithms, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Lemma 6.6, p.41 (printed) = PDF p.43

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_HSElemKernel_IsYes
import Definitions.Def_RevRedSAT_FiniteAlphabets
import Definitions.Def_RevRedSAT_IsHSCode

set_option autoImplicit false

namespace RevRedSAT

/-- **Lemma 6.6 (element kernel with budget k and solution lifting).**
Kundu, Panolan, Saurabh, Xue, Zehavi, *Reverse Reductions: From Faster SAT to Subexponential
Algorithms*, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Lemma 6.6, p.41: "For fixed d ≥ 2 and k ≥ 1, a d-Hitting Set instance I = (U, F, k) can be
reduced deterministically to an equivalent rank-d instance (U′, F′, k) with |U′| = O_d(k^{d−1}) and
|F′| = O_d(k^d). The budget remains k, and a solution of the reduced instance can be converted in
polynomial time into a solution of the original instance of size at most k. The preprocessing takes
f(d)|I|^{O(1)} + k^{O_d(1)} bit operations for a computable function f, with an absolute exponent on
|I|."

There are a computable `f : ℕ → ℕ` and an absolute exponent `c` such that for every `d ≥ 2` there
are finite-alphabet machines `M_red`, `M_lift` and constants `C, e` with: on every code `w` of a
`d`-Hitting Set instance `I` with `k ≥ 1`, `M_red` outputs within `f(d)·|w|^c + k^e` steps a code
`w'` of a `d`-Hitting Set instance `I'` with the same budget `k`, `|U'| ≤ C k^{d−1}`,
`|F'| ≤ C k^d`, and `I` is a YES-instance iff `I'` is; and for every solution `Y` of `I'` (a hitting
set of size at most `k`), `M_lift` on input `w`, `w'` and a listing of `Y` outputs within
`C·(|input| + 1)^e` steps a listing of a solution `X` of `I`.

**Formalization Note** The kernel is cited (Abu-Khzam, van Bevern) and not proved in the paper. The
lifting machine receives the original code, the reduced code and the reduced solution; "polynomial
time" is polynomial in that input with degree depending on `d`. -/
theorem lemma_6_6 :
    ∃ f : ℕ → ℕ, Computable f ∧ ∃ c : ℕ, ∀ d : ℕ, 2 ≤ d →
      ∃ Mred Mlift : Turing.TM2ComputableAux Bool Bool, FiniteAlphabets Mred ∧
        FiniteAlphabets Mlift ∧ ∃ (C : ℝ) (e : ℕ),
          ∀ (I : HSElemKernel.HSInstance) (w : List Bool), IsDHSCode d I w → 1 ≤ I.k →
            ∃ (I' : HSElemKernel.HSInstance) (w' : List Bool),
              IsDHSCode d I' w' ∧ I'.k = I.k ∧
              (I'.n : ℝ) ≤ C * (I.k : ℝ) ^ (d - 1) ∧ (I'.S.card : ℝ) ≤ C * (I.k : ℝ) ^ d ∧
              (HSElemKernel.IsYes I ↔ HSElemKernel.IsYes I') ∧
              HMBinPacking.OutputsWithin Mred w w' (f d * w.length ^ c + I.k ^ e) ∧
              ∀ LY : List (Fin I'.n), LY.Nodup → HSValid I' LY.toFinset →
                ∃ LX : List (Fin I.n), LX.Nodup ∧ HSValid I LX.toFinset ∧
                  HMBinPacking.OutputsWithin Mlift (w ++ w' ++ encSet LY) (encSet LX)
                    ⌊C * (((w ++ w' ++ encSet LY).length : ℝ) + 1) ^ e⌋₊ := by sorry

end RevRedSAT
