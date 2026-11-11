-- Prove2me | Theorems.Thm_SubexpPermanent_Main_theorem_1_1
-- name    : SubexpPermanent.Main.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:01:54.463478+00:00
-- url     : https://prove2.me/theorems/697c4b2b-a1ff-4fc5-9b24-a16a78f0e825
-- title:
--   Theorem 1.1 — deterministic polynomial time: $L\le\operatorname{per}(A)\le U$ with $\log(U/L)\lesssim n(\log\log n)^2/\log n$
-- statement:
--   There is one deterministic Turing machine $M$, one polynomial $p$ and one absolute constant $C$ with the following property. On input a matrix $A\in\mathbb Q^{n\times n}_{\ge0}$ with $\operatorname{per}(A)>0$, given in binary with total encoding length $S$, the machine halts within $p(S)$ steps. It outputs positive rational numbers $L$ and $U$ with
--   $$L\le\operatorname{per}(A)=\sum_{\pi\in S_n}\prod_{i=1}^nA_{i,\pi(i)}\le U,$$
--   and, for every $n\ge2$,
--   $$\log\frac UL\le C\,\frac{n(\log\log n)^2}{\log n}.$$
--   The approximation factor $\exp(O(n(\log\log n)^2/\log n))$ is subexponential. Earlier deterministic polynomial-time algorithms for nonnegative matrices achieved only factors $c^n$, from $e^n$ (Linial–Samorodnitsky–Wigderson) to $(\sqrt2)^n$ (Anari–Rezaei) and $(\sqrt2-\varepsilon)^n$. The theorem shows that every fixed $\alpha>1$ admits a deterministic polynomial-time $\alpha^n$ approximation.
--
--   **Formalization Note.** The machine is a Mathlib `Turing.FinTM2` with Boolean input and output alphabets. Its input is `encMat A`: the rows of $A$, each a list of rationals in lowest terms, in self-delimiting binary. Its output is `encRat L ++ encRat U`, and $S$ is the input length. $p$ and $C$ are fixed before $n$ and $A$, and the step bound is required on every admissible input. Inputs outside the theorem's domain (a negative entry, $\operatorname{per}(A)=0$) are unconstrained.
--
--   Differences from the source:
--
--   - encoding: a deterministic algorithm counting bit operations on a Turing machine → one Mathlib Turing.FinTM2 machine with Boolean input and output alphabets (Turing.TM2ComputableAux Bool Bool) that halts with the output code on its output stack, all other stacks empty, within t steps (Turing.TM2OutputsInTime); reason: a TM2 step runs one statement of a fixed finite program; a Turing machine and a bit-operation algorithm simulate each other with polynomial overhead, which the time bounds absorb
--   - encoding: A encoded by listing its entries, each as an integer numerator and a positive denominator in binary; S its total encoding length → input code encMat A (rows of rationals in lowest terms, self-delimiting binary) and S = |encMat A|; reason: a lowest-terms code is at most a constant factor longer than any numerator–denominator listing of the same entry, so a polynomial bound in its length is at least as strong
--   - encoding: poly(S) bit operations; log(U/L) ≲ … (absolute constant) → one p : Polynomial ℕ and one C : ℝ chosen before n and A, with t ≤ p(S) and log(U/L) ≤ C·n(log log n)²/log n; reason: the definitions of poly and ≲ (p. 2)
--   - generalization: asymptotic bounds in n hold for sufficiently large n (p. 2) → the bound log(U/L) ≤ C·n(log log n)²/log n for every n ≥ 2; reason: it specializes to ∃ N₀, ∀ n ≥ N₀; for n < N₀ the permanent can be computed exactly in polynomial time, giving L = U = per(A)
--   - encoding: returns positive rational numbers L and U → output code encRat L ++ encRat U; reason: binary code of the returned pair
-- source:
--   Kudria, Luo, Majid, Subexponential Approximation of the Permanent in Deterministic Polynomial Time, arXiv:2609.10516 (held PDF, sha256 e752b6f0…), p. 2, Theorem 1.1 (proved in §5, p. 18)

import Mathlib
import Definitions.Def_ContinualHardness_Linear_Encoding
import Definitions.Def_SubexpPermanent_Main_Machines
open ContinualHardness.Linear

namespace SubexpPermanent.Main

/-- Theorem 1.1 (polynomial time approximation), p. 2. -/
theorem theorem_1_1 :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (p : Polynomial ℕ) (C : ℝ),
      ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℚ),
        (∀ i j, 0 ≤ A i j) → 0 < A.permanent →
        ∃ (L U : ℚ) (t : ℕ),
          0 < L ∧ 0 < U ∧ L ≤ A.permanent ∧ A.permanent ≤ U ∧
          (2 ≤ n → Real.log ((U : ℝ) / L) ≤
            C * n * Real.log (Real.log n) ^ 2 / Real.log n) ∧
          OutputsWithin M (encMat A) (encRat L ++ encRat U) t ∧
          t ≤ p.eval (encMat A).length := by sorry

end SubexpPermanent.Main
