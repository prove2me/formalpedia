-- Prove2me | Theorems.Thm_RSCapacity_theorem_5_2
-- name    : RSCapacity.theorem_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:28:45.272717+00:00
-- url     : https://prove2.me/theorems/80638c46-04eb-4700-af35-8d53ee28c2ae
-- title:
--   Theorem 5.2 (Kopparty; prime-field form from BCPZZ): differential-equation root finding
-- statement:
--   Let $q$ be prime and $q\ge K>r$. Suppose $0\neq Q\in\mathbb F_q[X,Y_0,\dots,Y_r]$ satisfies $\deg_{Y_j}Q<q$ for all $j$ and
--   $$\deg_{(1,K-1,K-2,\dots,K-r-1)}Q<q^2 .$$
--   Then all $P\in\mathbb F_q[X]$ with $\deg P<K$ satisfying
--   $$Q(X,P,P^{[1]},\dots,P^{[r]})\equiv0$$
--   can be found in $q^{O(r+1)}$ time: there are an absolute constant $c$ and one deterministic program on the algebraic RAM that, given $Q$ by its monomials, outputs exactly these polynomials, each once, within $q^{c(r+1)}$ steps. Their number is at most $q^{4r+6}$.
--
--   This is Kopparty's root solver [Kop15, Theorem 4.3] in the prime-field form of [BCPZZ26, Theorem 2.1]; the paper cites it and uses it as the root-finding step of the decoder.
--
--   Differences from the source:
--   - reading: can be found in q^{O(r+1)} time (machine not stated) → the published algebraic RAM over ZMod q (MatroidSensOracle.aexec), one coin-free program, steps counting every instruction, halting within the bound for every word length w with bound < 2^w; the constant c is absolute; reason: field and word operations are both at most the step count; deterministic as in [BCPZZ26]
--   - reading: all P … can be found → the output list has no repetitions and its members are exactly the solutions of degree below K; reason: the strongest reading of finding all solutions
--   - encoding: Q as input → Q given by its monomials with nonzero coefficients, in any order (SparseRep); words [r, K, t, exponents], field cells the coefficients; reason: input layout; every order is accepted
--   - encoding: their number is at most q^{4r+6} → Set.encard ≤ q^{4r+6}; reason: finiteness is part of the claim
-- source:
--   Jeronimo, Algorithmic List Decoding at Capacity and Optimal Proximity Gaps for Reed–Solomon Codes, arXiv:2609.05870 (held version of November 1, 2026, sha256 9a0069bd…), Theorem 5.2, p.21 (PDF 23), citing Kopparty [Kop15, Theorem 4.3] and [BCPZZ26, Theorem 2.1]

import Mathlib
import Definitions.Def_MatroidSensOracle_AlgRAM
import Definitions.Def_RSCapacity_DiffSubst
import Definitions.Def_RSCapacity_DecoderIO

open Polynomial

set_option autoImplicit false

namespace RSCapacity

/-- **Theorem 5.2 (Kopparty; prime-field form from BCPZZ).** Jeronimo, arXiv:2609.05870 (held
version of November 1, 2026, sha256 9a0069bd…), Theorem 5.2, p.21 (PDF 23), citing Kopparty
[Kop15, Theorem 4.3] in the prime-field form of [BCPZZ26, Theorem 2.1]. Let q be prime and
q ≥ K > r. Suppose 0 ≠ Q ∈ 𝔽_q[X, Y_0, …, Y_r] satisfies deg_{Y_j} Q < q for all j and
deg_{(1,K−1,K−2,…,K−r−1)} Q < q². Then all P ∈ 𝔽_q[X] with deg P < K satisfying
Q(X, P, P^{[1]}, …, P^{[r]}) ≡ 0 can be found in q^{O(r+1)} time. Their number is at most q^{4r+6}.

**Formalization Note.**
* "Found in q^{O(r+1)} time": one coin-free (deterministic) program of the published algebraic RAM
  `MatroidSensOracle.aexec` over 𝔽_q = `ZMod q` and one absolute constant c, chosen before q, r, K
  and Q, such that the program halts within q^{c(r+1)} steps (every instruction counts) for every
  word length w with q^{c(r+1)} < 2^w, and outputs every such P exactly once and nothing else
  (`OutputsExactly`).
* Input: Q is given sparsely, as its monomials with nonzero coefficients in any order
  (`SparseRep`); words `[r, K, t, exponents…]`, field cells the t coefficients.
* The number of solutions is `Set.encard`, so finiteness is part of the claim. -/
theorem theorem_5_2 :
    ∃ c : ℕ, ∃ prog : List MatroidSensOracle.AInstr, (∀ ins ∈ prog, ¬ ins.IsCoin) ∧
      ∀ (q : ℕ) [Fact q.Prime] (r K : ℕ), r < K → K ≤ q →
      ∀ Q : MvPolynomial (Fin (r + 2)) (ZMod q), Q ≠ 0 →
        (∀ j : Fin (r + 1), Q.degreeOf j.succ < q) →
        Q.weightedTotalDegree (diffWeight K r) < q ^ 2 →
        (∀ ts : List ((Fin (r + 2) →₀ ℕ) × ZMod q), SparseRep ts Q →
          ∀ w : ℕ, q ^ (c * (r + 1)) < 2 ^ w →
            ∃ st, MatroidSensOracle.aexec prog (fun _ => 0) (q ^ (c * (r + 1))) 0 0
                (MatroidSensOracle.aloadWords w (diffEqWords r K ts))
                (MatroidSensOracle.aloadFields (ts.map Prod.snd)) = some st ∧
              OutputsExactly K st {P : (ZMod q)[X] | P.degree < K ∧ diffEval Q P = 0}) ∧
        {P : (ZMod q)[X] | P.degree < K ∧ diffEval Q P = 0}.encard ≤
          ((q ^ (4 * r + 6) : ℕ) : ℕ∞) := by sorry

end RSCapacity
