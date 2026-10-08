-- Prove2me | Theorems.Thm_TheoryOfGames_ThreePerson_strategic_equivalence_isomorphism
-- name    : TheoryOfGames.ThreePerson.strategic_equivalence_isomorphism
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T08:25:00.946635+00:00
-- url     : https://prove2.me/theorems/351685c9-fbae-48a4-9484-94e4db8a3f1c
-- title:
--   (31:Q) — strategically equivalent games have isomorphic imputations, domination and solutions
-- statement:
--   Let $v$ be a characteristic function of a zero-sum $n$-person game $\Gamma$ (satisfying (25:3:a)–(25:3:c)), and let $v'$ be strategically equivalent to $v$, i.e. $v'(S) = v(S) + \sum_{k \in S}\alpha^0_k$ for constants with $\sum_k \alpha^0_k = 0$ (27:1), (27:2). Then there exists a mapping $f$ of vectors to vectors with:
--
--   1. $f$ maps the imputations of $v$ one-to-one onto the imputations of $v'$;
--   2. for every imputation $\vec\alpha$ of $v$ and every set $S$: $S$ is effective for $\vec\alpha$ under $v$ iff $S$ is effective for $f(\vec\alpha)$ under $v'$;
--   3. for imputations $\vec\alpha, \vec\beta$ of $v$: $\vec\alpha \succ \vec\beta$ under $v$ iff $f(\vec\alpha) \succ f(\vec\beta)$ under $v'$;
--   4. for every set $V$ of imputations of $v$: $V$ is a solution for $v$ iff $f(V)$ is a solution for $v'$.
--
--   This is what allows the book to study any game through its reduced form: the determination of all solutions in §32 is carried out for the reduced three-person game (32:1) and transfers to every game strategically equivalent to it.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), pp. 281–282, 31.3.1–31.3.3, (31:15), (31:16), (31:Q)

import Mathlib
import Definitions.Def_TheoryOfGames_ThreePerson_Solution
import Definitions.Def_TheoryOfGames_CharFun_StrategicEquivalence

namespace TheoryOfGames.ThreePerson

/-- (31:Q), 31.3.3: if two zero-sum games with characteristic functions `v` and `v'` are
strategically equivalent, then there exists a one-to-one mapping of the imputations of `v` onto
those of `v'` which carries effective sets, domination and solutions of `v` into those of `v'`. -/
theorem strategic_equivalence_isomorphism {n : ℕ} (v v' : Finset (Fin n) → ℝ)
    (hv : TheoryOfGames.CharFun.IsCharFunction v) (hequiv : TheoryOfGames.CharFun.StrategicallyEquivalent v v') :
    ∃ f : (Fin n → ℝ) → (Fin n → ℝ),
      Set.BijOn f {α | IsImputation v α} {α' | IsImputation v' α'} ∧
      (∀ α : Fin n → ℝ, IsImputation v α →
        ∀ S : Finset (Fin n), IsEffective v S α ↔ IsEffective v' S (f α)) ∧
      (∀ α β : Fin n → ℝ, IsImputation v α → IsImputation v β →
        (Dominates v α β ↔ Dominates v' (f α) (f β))) ∧
      (∀ V : Set (Fin n → ℝ), (∀ α ∈ V, IsImputation v α) →
        (IsSolution v V ↔ IsSolution v' (f '' V))) := by sorry

end TheoryOfGames.ThreePerson
