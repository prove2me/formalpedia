-- Prove2me | Theorems.Thm_ReLUSynth_Boolean_lemma_4_5
-- name    : ReLUSynth.Boolean.lemma_4_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:12:59.006233+00:00
-- url     : https://prove2.me/theorems/a34d8547-293e-4f2b-b0d0-da7802f4040e
-- title:
--   Lemma 4.5 — exact-sum blocker existence is Σ₂ᴾ-complete, even restricted (prime q ≥ 5, p = q − 1, β_j ≡ 3, T ≡ 0 mod q, n > p)
-- statement:
--   Deciding whether an exact-sum blocker of size at most $p$ exists is $\Sigma_2^P$-complete under deterministic polynomial-time many-one reductions. Moreover, every $\Sigma_2^P$ language reduces to it by such a reduction $f$, with a polynomial $\pi$, such that every image $f(u)$ is a well-formed instance $(\beta_1,\dots,\beta_n,T,p)$ satisfying: there is a prime $q\ge5$ with $p=q-1$; every $\beta_j$ has $0<\beta_j<T$, is not a power of two, and
--   $$\beta_j\equiv3\pmod q,\qquad T\equiv0\pmod q;$$
--   $n>p$; and $p\le\pi(|u|)$.
--
--   This is the source problem of the reduction proving Theorem 4.12.
--
--   Differences from the source:
--   - encoding: integers in binary, rationals as signed numerator and positive denominator, explicitly listed graphs and lists (p. 9); languages are sets of binary strings (p. 12) → the fixed prefix-free codes encNat (self-delimiting binary), encInt, encRat, encList, Circuit.encode, and a string is in the language only if it is the code of a well-formed yes instance; reason: the paper fixes no concrete code; these are injective with linear overhead, so membership and hardness do not depend on the choice
--   - encoding: Σ₂ᴾ: ∃ a polynomial-length string ∀ a polynomial-length string, polynomial-time predicate; deterministic polynomial-time many-one reductions (pp. 12–13, 16) → the published AvgWorstGap.InSigmaP 2 / IsSigmaPComplete 2 / ComputesFn (certificates of exact length v(|x|), multi-tape NKtLB.Machine); reason: the standard definition; fixed-length certificates are equivalent to bounded ones by padding (the paper's own 'padded as necessary', p. 16)
--   - reading: Σ₂ᴾ-complete even under the restrictions; the reduction produces p bounded by a polynomial in its input length; every produced instance has n > p → IsSigmaPComplete 2 of the blocker language, and every Σ₂ᴾ language reduces to it by a reduction whose every image satisfies BlockerInstance.Restricted and p ≤ π(|u|); reason: the restrictions are properties of the produced instances
--   - encoding: an odd prime q ≥ 5 is supplied → the instance stores (β, T, p); Restricted asks for a prime q ≥ 5 with p = q − 1; reason: q = p + 1 is determined by p; 'odd' is implied by q ≥ 5 prime
-- source:
--   Myrisiotis, The Complexity of ReLU Network Synthesis from a Parameter Multiset, arXiv:2611.04074v1, p. 17, Lemma 4.5

import Mathlib
import Definitions.Def_ReLUSynth_Boolean_Blocker

namespace ReLUSynth.Boolean

/-- Lemma 4.5 (p. 17): deciding whether an exact-sum blocker exists is `Σ_2^P`-complete under
deterministic polynomial-time many-one reductions; moreover every `Σ_2^P` language reduces to it
by such a reduction whose every image is a well-formed instance satisfying the restrictions
(an odd prime `q ≥ 5` with `p = q − 1`, `0 < β_j < T`, no `β_j` a power of two, `β_j ≡ 3`,
`T ≡ 0 (mod q)`, `n > p`), with `p` bounded by a polynomial in the reduction's input length. -/
theorem lemma_4_5 :
    AvgWorstGap.IsSigmaPComplete 2 BlockerLang ∧
    ∀ L' : Set (List Bool), AvgWorstGap.InSigmaP 2 L' →
      ∃ π : Polynomial ℕ, ReducesWithImages L' BlockerLang (fun u s => ∃ I : BlockerInstance,
        s = I.encode ∧ I.WellFormed ∧ I.Restricted ∧ I.p ≤ π.eval u.length) := by sorry

end ReLUSynth.Boolean
