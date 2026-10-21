-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P14_pathIdempotent_expectation
-- name    : QAlgorithms.Papers.Independent.Support21.P14.pathIdempotent_expectation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:27:11.893522+00:00
-- url     : https://prove2.me/theorems/cd9ad45f-73b0-485b-9838-d8ab0ccae10e
-- title:
--   Conditional expectation of a canonical path idempotent
-- statement:
--   Let $F$ be a field and $A_0\subseteq\cdots\subseteq A_n$ a finite tower of finite-dimensional split semisimple unital $F$-algebras, with $A_0=F$, $n\ge1$, and multiplicity-free inclusions. Let $\varepsilon:A_n\to F$ be a trace whose restriction to $A_{n-1}$ is faithful in the sense that $\varepsilon(ab)=0$ for every $b\in A_{n-1}$ implies $a=0$. Let $E_n:A_n\to A_{n-1}$ be a trace-preserving conditional expectation: an $F$-linear $A_{n-1}$-bimodule retraction. For a branching path $T$, let $p_T$ be the canonical product of its embedded minimal central idempotents, and let $T'$ be its length-$(n-1)$ prefix. Then
--   $$E_n(p_T)=\frac{\varepsilon(p_T)}{\varepsilon(p_{T'})}\,p_{T'}.$$
--   The trace on $A_n$ need not be faithful. This identifies the conditional-expectation coefficient for the canonical path system.
--
--   **Formalization Note** The split-block and actual restriction-intertwiner definitions are reused from the pinned accepted library. Only levels at most $n$ satisfy tower hypotheses; a type family outside that finite segment is unused.
-- source:
--   Cyclotomic Birman--Wenzl--Murakami algebras, II: Admissibility Relations and Freeness, arXiv:math/0612065v5, PDF p. 16, Lemma 2.19: expectation of a path idempotent

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P14

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Support21.P14

/-- Lemma 2.19, PDF p.16. Faithfulness is nondegeneracy of the
restricted trace pairing. The trace on A_n may be degenerate. E is a
bimodule retraction preserving the trace, not an analytic expectation. -/
theorem pathIdempotent_expectation {F : Type*} [Field F] {A : ℕ → Type*}
    [∀ k, Ring (A k)] [∀ k, Algebra F (A k)]
    (n : ℕ) (hn : 1 ≤ n) (D : FiniteSplitTower F A n)
    (epsilon : A n →ₗ[F] F) (htrace : ∀ a b, epsilon (a*b) = epsilon (b*a))
    (E : A n →ₗ[F] A (n-1))
    (hretract : ∀ a, E (D.inc (n-1) n (by omega) le_rfl a) = a)
    (hbimodule : ∀ a b : A (n-1), ∀ x : A n,
      E (D.inc (n-1) n (by omega) le_rfl a * x *
        D.inc (n-1) n (by omega) le_rfl b) = a * E x * b)
    (hpreserve : ∀ x, epsilon (D.inc (n-1) n (by omega) le_rfl (E x)) = epsilon x)
    (hfaithful : ∀ a : A (n-1),
      (∀ b : A (n-1), epsilon (D.inc (n-1) n (by omega) le_rfl (a*b)) = 0) → a = 0)
    (t : FiniteTowerPath D) :
    E (finitePathIdempotent D t n le_rfl) =
      (epsilon (finitePathIdempotent D t n le_rfl) /
        epsilon (D.inc (n-1) n (by omega) le_rfl
          (finitePathIdempotent D t (n-1) (by omega)))) •
        finitePathIdempotent D t (n-1) (by omega) := by sorry

end QAlgorithms.Papers.Independent.Support21.P14

end
