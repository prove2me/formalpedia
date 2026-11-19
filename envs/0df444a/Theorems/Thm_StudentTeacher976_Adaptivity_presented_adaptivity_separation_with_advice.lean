-- Prove2me | Theorems.Thm_StudentTeacher976_Adaptivity_presented_adaptivity_separation_with_advice
-- name    : StudentTeacher976.Adaptivity.presented_adaptivity_separation_with_advice
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T13:37:12.775724+00:00
-- url     : https://prove2.me/theorems/65917c06-a692-4a23-bda9-d7b991711fba
-- title:
--   The fixed-presentation adaptivity separation excludes advice students
-- statement:
--   Fix $i\ge0$ and assume $\Sigma_{i+1}^p\not\subseteq\Delta_{i+1}^p/\mathrm{poly}$. Let $r$ and $q$ satisfy the admissibility conditions of Theorem 1.4, including monotonicity, unboundedness and the positive sublinear bound for $r$.
--
--   There exist a total search relation $R$ and one faithful refutation presentation $P$ of $R$ such that:
--
--   1. A uniform $\mathrm{FP}^{\Sigma_i^p}$ student wins with this presentation in $r(m)+1$ rounds and one query per round.
--   2. No student realized by $\mathrm{FP}^{\Sigma_i^p}/\mathrm{poly}$ wins with this same presentation in $r(m)$ rounds and $q(m)$ simultaneous queries per round.
--
--   Writing $W_{a,b}(P)$ for uniform solvability of the fixed presentation, and $W^{\mathrm{adv}}_{a,b}(P)$ for solvability with polynomial advice,
--
--   $$
--   \exists R\,\exists P\text{ presenting }R,\qquad
--   W_{r+1,1}(P)\;\wedge\;\neg W^{\mathrm{adv}}_{r,q}(P).
--   $$
--
--   Advice is shared by all student inputs of each encoded input length and need not be computable. The result strengthens the lower bound for a fixed presentation to exclude advised students. Both resource budgets and the refutation presentation are kept fixed in the comparison. It does not assert noninclusion between classes that permit arbitrary replacement presentations of the underlying relation.
-- source:
--   Strengthening of the fixed-presentation argument in Ježil–Tsintsilidas, Parallelism and Adaptivity in Student-Teacher Witnessing, STOC 2027 submission #976, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/976.pdf, Theorem 1.4 p.7, proof §3.1 pp.19–21, Claim 3.1 p.20, Appendix A pp.39–40. The lower student is allowed polynomial advice, which is incorporated in the decision algorithm’s polynomial advice.

import Definitions.Def_StudentTeacher976_Adaptivity_Game
import Definitions.Def_StudentTeacher976_Adaptivity_AdviceSelectors
set_option autoImplicit false
open QAdvFew.PoQOracle StudentTeacher976.Adaptivity
open AdviceComputations (InFPAdvice)

theorem StudentTeacher976.Adaptivity.presented_adaptivity_separation_with_advice (i : ℕ) (hardness : ¬StudentTeacher976.Adaptivity.Sigma (i+1)⊆DeltaPoly i)
    (r q : ℕ → ℕ) (hr : AdmissibleRounds r) (hq : AdmissibleQueries q) :
    ∃ (R : SearchRelation) (P : RefutablePresentation i R),
      (∃ g : Student,UniformStudent i g ∧
        StudentShape P (fun m => r m+1) (fun _ => 1) g ∧
        StudentWins P (fun m => r m+1) (fun _ => 1) g) ∧
      ¬∃ g : Student,
        (∃ F : Word → Word,InFPAdvice i F ∧ ∀ (x : Word) (t : ℕ) (H : List (List Word)),
          F (tup [x,List.replicate (t+1) true,tup (H.map tup)])=tup (g x t H)) ∧
        StudentShape P r q g ∧ StudentWins P r q g := by sorry
