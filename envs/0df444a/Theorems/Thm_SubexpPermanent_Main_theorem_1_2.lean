-- Prove2me | Theorems.Thm_SubexpPermanent_Main_theorem_1_2
-- name    : SubexpPermanent.Main.theorem_1_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:01:46.080091+00:00
-- url     : https://prove2.me/theorems/aafbe71e-a148-4590-92ff-cbaf4fe4fd52
-- title:
--   Theorem 1.2 — accuracy vs. time: $\log(U/L)\le 2n/\sqrt{3\lambda}+8\eta n$ in time $\mathrm{poly}\cdot e^{O(\sqrt\lambda\log^2(\lambda/\eta))}$
-- statement:
--   There is a deterministic Turing machine, and there are absolute constants $C$ and $d$, with the following property. The machine takes a matrix $A\in\mathbb Q^{n\times n}_{\ge0}$ with $\operatorname{per}(A)>0$ and total encoding length $S$, together with rational parameters $\lambda\ge1$ and $0<\eta\le1/100$. It returns positive rational numbers $L$ and $U$ with
--   $$L\le\operatorname{per}(A)\le U,\qquad \log\frac UL\le\frac{2n}{\sqrt{3\lambda}}+8\eta n\qquad(1),$$
--   within
--   $$C\,(S+n+\operatorname{bits}\lambda+\operatorname{bits}\eta+\lambda+\eta^{-1})^d\,\exp\!\Big(C\sqrt\lambda\,\log^2\frac\lambda\eta\Big)\qquad(2)$$
--   steps. Increasing $\lambda$ improves the accuracy and costs running time. Choosing $\sqrt\lambda\asymp\log n/(\log\log n)^2$ and $\eta\asymp1/\sqrt\lambda$ gives Theorem 1.1.
--
--   **Formalization Note.** The input is `encMat A ++ encRat λ ++ encRat η` and the output `encRat L ++ encRat U`. $S$ is the length of `encMat A`, and $\operatorname{bits}x$ the length of `encRat x`. The parameter is named `lam` in Lean.
--
--   Differences from the source:
--
--   - encoding: a deterministic algorithm counting bit operations on a Turing machine → one Mathlib Turing.FinTM2 machine with Boolean input and output alphabets (Turing.TM2ComputableAux Bool Bool) that halts with the output code on its output stack, all other stacks empty, within t steps (Turing.TM2OutputsInTime); reason: a TM2 step runs one statement of a fixed finite program; a Turing machine and a bit-operation algorithm simulate each other with polynomial overhead, which the time bounds absorb
--   - encoding: A encoded by listing its entries, each as an integer numerator and a positive denominator in binary; S its total length; bits(x) the length of the binary encoding of x → input code encMat A ++ encRat λ ++ encRat η (rationals in lowest terms, self-delimiting binary); S = |encMat A|, bits x = |encRat x|; reason: a lowest-terms code is at most a constant factor longer than any numerator–denominator listing of the same entry, so a bound in its length is at least as strong
--   - reading: poly(S + n + bits λ + bits η, λ, η⁻¹)·exp(O(√λ log²(λ/η))), with absolute polynomial degree and implicit constant → ∃ C : ℝ, ∃ d : ℕ fixed before every input with t ≤ C·(S + n + bits λ + bits η + λ + η⁻¹)^d·exp(C·√λ·log²(λ/η)); reason: explicit absolute constant and degree; the base is at least 1, so C·base^d dominates every polynomial of degree d in the three arguments with bounded coefficients
--   - encoding: returns positive rational numbers L and U → output code encRat L ++ encRat U; reason: binary code of the returned pair
-- source:
--   Kudria, Luo, Majid, Subexponential Approximation of the Permanent in Deterministic Polynomial Time, arXiv:2609.10516 (held PDF, sha256 e752b6f0…), p. 2, Theorem 1.2, eqs. (1)–(2)

import Mathlib
import Definitions.Def_ContinualHardness_Linear_Encoding
import Definitions.Def_SubexpPermanent_Main_Machines
open ContinualHardness.Linear

namespace SubexpPermanent.Main

/-- Theorem 1.2 (approximation versus running time), p. 2. -/
theorem theorem_1_2 :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℝ) (d : ℕ),
      ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℚ) (lam η : ℚ),
        (∀ i j, 0 ≤ A i j) → 0 < A.permanent → 1 ≤ lam → 0 < η → η ≤ 1 / 100 →
        ∃ (L U : ℚ) (t : ℕ),
          0 < L ∧ 0 < U ∧ L ≤ A.permanent ∧ A.permanent ≤ U ∧
          Real.log ((U : ℝ) / L) ≤ 2 * n / Real.sqrt (3 * lam) + 8 * η * n ∧
          OutputsWithin M (encMat A ++ encRat lam ++ encRat η) (encRat L ++ encRat U) t ∧
          (t : ℝ) ≤ C * ((((encMat A).length + n + (encRat lam).length + (encRat η).length : ℕ) : ℝ)
              + lam + η⁻¹) ^ d *
            Real.exp (C * Real.sqrt lam * Real.log ((lam : ℝ) / η) ^ 2) := by sorry

end SubexpPermanent.Main
