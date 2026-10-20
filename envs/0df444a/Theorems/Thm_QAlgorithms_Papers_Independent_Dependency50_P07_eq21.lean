-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P07_eq21
-- name    : QAlgorithms.Papers.Independent.Dependency50.P07.eq21
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:30:24.821931+00:00
-- url     : https://prove2.me/theorems/a512607e-5c6e-409f-85eb-7c285010dc2f
-- title:
--   Equality-constrained optimization and the constant region
-- statement:
--   For a finite cq ensemble $XQ$, let $D^*(R)=\sup_{U|X}\{I(U;Q):I(U;X)-I(U;Q)\le R\}$. For $0\le R\le H(X|Q)$ the equality-constrained feasible set is nonempty and has an attaining optimizer, and
--
--   $$D^*(R)=\max_{U|X:\ I(U;X)-I(U;Q)=R} I(U;Q).$$
--
--   For every $R\ge H(X|Q)$ with $R\ge0$,
--
--   $$D^*(R)=D(\infty)=I(X;Q).$$
--
--   Here $D(\infty)$ is the supremum of operational excess randomness over finite nonnegative communication rates. These identities isolate the nonconstant portion of the cq trade-off.
-- source:
--   Distilling common randomness from bipartite quantum states, arXiv:quant-ph/0304196v2, PDF p. 12, §2, Remark (21): equality constraint and saturation

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P07

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder

open Filter

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Information100.P04 (Measurement)

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Dependency50.P07

section CQStatements

variable {X Q Y T : Type} [Fintype X] [Fintype Q] [Fintype Y] [Fintype T]
  [DecidableEq X] [DecidableEq Q] [DecidableEq Y] [DecidableEq T]
  [Nonempty X] [Nonempty Q] [Nonempty Y] [Nonempty T]

/-- PDF p.12, (21): an attaining equality-constrained optimizer on its nonempty domain,
and saturation above H(X|Q). No empty equality-constrained supremum is introduced. -/
theorem eq21 (E : CQData X Q) (hE : E.Valid) :
    (∀ R : ℝ, 0 ≤ R → R ≤ classicalGivenQuantum E →
      ∃ V : Auxiliary X, auxCost E V = R ∧ auxIQ E V = dStar E R ∧
        ∀ W : Auxiliary X, auxCost E W = R → auxIQ E W ≤ auxIQ E V) ∧
    (∀ R : ℝ, 0 ≤ R → classicalGivenQuantum E ≤ R →
      dStar E R = total (cqDensity E) ∧ total (cqDensity E) = ensembleInformation E) := by sorry

end CQStatements

end QAlgorithms.Papers.Independent.Dependency50.P07

end
