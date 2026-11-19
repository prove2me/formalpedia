-- Prove2me | Theorems.Thm_PolyTimeFactorization_polytime_semiprime_factorization
-- name    : PolyTimeFactorization.polytime_semiprime_factorization
-- status  : Open
-- author  : @LG
-- created : 2026-11-16T16:13:36.506757+00:00
-- url     : https://prove2.me/theorems/24cccb9e-b23a-4088-9ab3-7f29e627baca
-- title:
--   Polynomial-time semiprime factorization (goal)
-- statement:
--   There exists a total function $f:\mathbb{N}\to\mathbb{N}\times\mathbb{N}$, computable in polynomial time by a classical Turing machine, that factors every semiprime: for all primes $p$ and $q$ (possibly equal),
--   $$f(pq)=(\min(p,q),\,\max(p,q)).$$
--   Polynomial time is measured in the bit-length of the input: one machine and one fixed polynomial bound must serve every input, under the standard binary encoding of $\mathbb{N}$.
--
--   Whether such an $f$ exists is a central open problem of computational number theory. No classical polynomial-time factoring algorithm is known, and no superpolynomial lower bound is known either. A proof of existence would break RSA; a proof of nonexistence would imply $\mathrm{P}\ne\mathrm{NP}$. This is the asymptotic, theorem-shaped core of Epoch AI's FrontierMath problem on improving the best-known classical factorization algorithms.
--
--   **Formalization Note.** Polynomial-time computability is Mathlib's `Turing.TM2ComputableInPolyTime` with input encoding `encodeNat` (binary) and output encoding `encodingProd encodingNatBool encodingNatBool`; because that notion is a bundled structure rather than a proposition, its existence is expressed with `Nonempty`. Fixing the binary encoding rules out machines whose time bound is polynomial in the value of the input rather than its bit-length.
-- source:
--   Epoch AI, FrontierMath: Open Problems - Improve the Best-known Classical Factorization Algorithms, https://epoch.ai/frontiermath/open-problems/prime-factorization (asymptotic formalization; see the mission description for the precise relationship). The polynomial-time factoring question is classical; cf. https://en.wikipedia.org/wiki/Integer_factorization

import Mathlib
open Computability Turing

namespace PolyTimeFactorization

theorem polytime_semiprime_factorization :
    ∃ f : ℕ → ℕ × ℕ,
      Nonempty (TM2ComputableInPolyTime encodeNat (encodingProd encodingNatBool encodingNatBool).encode f) ∧
      ∀ p q : ℕ, p.Prime → q.Prime → f (p * q) = (min p q, max p q) := by sorry

end PolyTimeFactorization
