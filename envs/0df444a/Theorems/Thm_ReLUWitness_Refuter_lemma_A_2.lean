-- Prove2me | Theorems.Thm_ReLUWitness_Refuter_lemma_A_2
-- name    : ReLUWitness.Refuter.lemma_A_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T06:55:34.58744+00:00
-- url     : https://prove2.me/theorems/1655f6ef-05a3-4738-a902-dfabcdf8cf1b
-- title:
--   Lemma A.2 — short rational disagreement: a network differing from MAX_n differs at a rational point of polynomial code length
-- statement:
--   Networks are coded by the exact record of §2.3 with rational weights and biases stored as unreduced pairs, and $|x|$ is the length of the binary string code of a vector (an exact tuple of rational pairs under the pairing $\langle u,v\rangle=(u+v)(u+v+1)+2v$).
--
--   **Lemma A.2.** There is a polynomial $p_0$ with nonnegative integer coefficients such that, for every $n$ and every network code $N$ with $\mathrm{Net}(N,n)$: if $N\ne\mathrm{MAX}_n$ on $\mathbb R^n$, then some valid rational $n$-vector $x$ satisfies
--
--   $$|x|\le p_0(|N|)\qquad\text{and}\qquad N(x)\ne\mathrm{MAX}_n(x).$$
--
--   The bound connects agreement on all real inputs with the bounded test $\forall x\,(|x|\le p(|N|)\to\neg\mathrm{Err}(N,n,x))$ used by the correctness predicate, and its $p_0$ is the first summand of the common cutoff $p$ of Theorem 8.5. It is ordinary mathematics in the standard model, not an internal statement of the arithmetic theory.
--
--   Differences from the source:
--   - encoding: network code, Net(N,n), code length, valid rational n-vector → the same predicates read in the standard model (numbers ℕ, strings finite subsets of ℕ, primitives with their intended values); reason: the lemma is a standard-model statement (Appendix A)
--   - encoding: N ≠ MAX_n on ℝ^n → some z : ℕ → ℝ with N(z) ≠ MAX_n(z), the network reading the coordinates 0, …, n−1; reason: coordinates beyond n are never read, so this is the same set of inputs
--   - encoding: polynomial with nonnegative integer coefficients → Polynomial ℕ, evaluated at |N|; reason: same objects
-- source:
--   Myrisiotis, A Witnessing Duality for ReLU Network Depth, arXiv:2610.38281v1, p. 66, Lemma A.2

import Mathlib
import Definitions.Def_ReLUWitness_Refuter_Standard

namespace ReLUWitness.Refuter

/-- Lemma A.2 (Short rational disagreement). There is a polynomial `p₀` with nonnegative
integer coefficients such that every valid network code `N` (`Net(N,n)` in the standard
model) with `N ≠ MAX_n` on `ℝ^n` disagrees with `MAX_n` at a valid rational `n`-vector `x`
of code length `|x| ≤ p₀(|N|)`. -/
theorem lemma_A_2 : ∃ p₀ : Polynomial ℕ, ShortRationalDisagreement p₀ := by sorry

end ReLUWitness.Refuter
