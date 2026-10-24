-- Prove2me | Theorems.Thm_SKAlgorithm_Qudit_theorem_1
-- name    : SKAlgorithm.Qudit.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:16:07.073993+00:00
-- url     : https://prove2.me/theorems/19e11b47-5c62-4323-be91-479043fd96b4
-- title:
--   Theorem 1, p. 4 — Solovay-Kitaev: every gate in SU(d) has an ε-approximating instruction sequence of length O(log^{ln 5/ln(3/2)}(1/ε))
-- statement:
--   **Theorem (Solovay-Kitaev).** Let $\mathcal G$ be an instruction set for $SU(d)$. There is a constant $C > 0$ such that for every accuracy $\epsilon > 0$ and every gate $U \in SU(d)$ there is a finite sequence $S$ of gates from $\mathcal G$ with
--   $$|S| \le C \, \ln\!\left(2 + \frac1\epsilon\right)^{\ln 5/\ln(3/2)} \qquad \text{and} \qquad d(U, S) < \epsilon .$$
--
--   Here $d(U, S) = \|U - S\|$ is the operator-norm distance between $U$ and the product of the gates of $S$, and $\ln 5/\ln(3/2) \approx 3.97$. Theorem 1 asserts length $O(\log^c(1/\epsilon))$ for some constant $c$; the Solovay-Kitaev algorithm described in the paper gives $c = \ln 5/\ln(3/2)$ (Eq. (8), and §5.1 for qudits), and that is the exponent stated here. The theorem says that any universal instruction set simulates any other with only polylogarithmic overhead in the accuracy.
--
--   **Formalization Note.** The constant $C$ depends only on $d$ and $\mathcal G$ and is chosen before $\epsilon$ and $U$; this order is the content of the $O(\cdot)$. $\log(1/\epsilon)$ is replaced by $\ln(2 + 1/\epsilon)$ so that the bound is positive for every $\epsilon > 0$; as $\epsilon \to 0$ the two are asymptotically equivalent, so the class $O(\log^{3.97}(1/\epsilon))$ is unchanged. Instruction sets are as in Definition 1: finite, closed under $\dagger$, universal.
-- source:
--   Dawson and Nielsen, The Solovay-Kitaev algorithm, arXiv:quant-ph/0505030v2, p. 4, Theorem 1; exponent from p. 7, Eq. (8), and p. 11, §5.1

import Mathlib
import Definitions.Def_SKAlgorithm_Qudit_Model

open scoped Matrix
open QAlgorithms

namespace SKAlgorithm.Qudit

theorem theorem_1 (d : ℕ) (G : Finset (SU d)) (hG : IsInstructionSet G) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ∀ U : SU d,
      ∃ S : List (SU d), (∀ g ∈ S, g ∈ G) ∧
        (S.length : ℝ) ≤ C * Real.log (2 + 1 / ε) ^ (Real.log 5 / Real.log (3 / 2)) ∧
        opDist U (seqUnitary S) < ε := by sorry

end SKAlgorithm.Qudit
