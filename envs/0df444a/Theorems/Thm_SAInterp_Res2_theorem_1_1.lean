-- Prove2me | Theorems.Thm_SAInterp_Res2_theorem_1_1
-- name    : SAInterp.Res2.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:37:45.547724+00:00
-- url     : https://prove2.me/theorems/f4c56124-6edc-4c31-94b0-646b353568cb
-- title:
--   Theorem 1.1 — Sherali-Adams does not polynomially simulate Res(2): CNFs with poly-size Res(2) refutations need Sherali-Adams size 2^Ω(n^{1/3})
-- statement:
--   Sherali-Adams refutations are taken in the dual-variable encoding (Definition 2.3) and $\mathrm{Res}(2)$ refutations as in Definition 8.3. Theorem 1.1 has two parts.
--
--   **(a)** Sherali-Adams does not polynomially simulate $\mathrm{Res}(2)$: there is no constant $K$ such that every unsatisfiable CNF $F$ over a finite set of variables with a $\mathrm{Res}(2)$ refutation of size $s$ has a Sherali-Adams refutation of size at most $K(s+|F|)^K+K$.
--
--   **(b)** There are an infinite set $I\subseteq\mathbb N$, for each $n\in I$ an unsatisfiable CNF $F_n$ over exactly the $n$ variables $x_1,\dots,x_n$ (all of which occur), and constants $C$, $c>0$, $n_0$ such that for every $n\in I$:
--   $$|F_n|\le Cn^C+C,\qquad F_n\text{ has a }\mathrm{Res}(2)\text{ refutation of size}\le Cn^C+C,$$
--   $$n\ge n_0\ \Longrightarrow\ \text{every Sherali-Adams refutation of }F_n\text{ has size}\ \ge 2^{c\,n^{1/3}}.$$
--
--   The family is $\mathrm{CPLS}^{\mathrm{bool}}_{2^\ell}\circ\oplus$, whose number of variables is $\Theta(2^{3\ell})$, which explains the exponent $1/3$. The result separates Sherali-Adams exponentially from the depth-1 fragment $\mathrm{Res}(2)$ of bounded-depth Frege.
--
--   Differences from the source:
--   - reading: "does not polynomially-simulate" → no constant K with SA-size ≤ K(s + |F|)^K + K for every unsatisfiable CNF with a size-s Res(2) refutation; reason: the negation of polynomial simulation by size; it is stronger than "no polynomial-time translation".
--   - reading: "infinite family of polynomial-size n-variate CNF formulas {F_n}" → an infinite index set I, F_n over `Fin n` with all n variables occurring, |F_n| ≤ C n^C + C, one family and one set of constants; reason: the explicit meaning of the printed sentence.
--   - reading: 2^{Ω(n^{1/3})} → ∃ c > 0, ∃ n0, ∀ n ∈ I with n ≥ n0; reason: Ω with explicit constants fixed before n.
--   - reading: |F| → number of clauses plus literal occurrences; Res(2) size → Σ over lines of (1 + literal occurrences); reason: each is within a constant factor of a symbol count.
--   - reading: SA size, "the (maximum) number of monomials … before cancellations" → total number of monomials of all expanded products; reason: the readings differ by a factor polynomial in n, so (a) and (b) are the same statements under both.
-- source:
--   Acheampong, Davis, Robere, Polynomial Interpolation for Sherali-Adams Lower Bounds, STOC 2027 submission (manuscript sha256 8de0a787…), p. 1 (PDF p. 3), Theorem 1.1; proved p. 46 (PDF p. 48) from Theorem 8.2

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_CNF
import Definitions.Def_SAInterp_Res2_SherAdams
import Definitions.Def_SAInterp_Res2_ResK

open MultiplierAssoc206.Resolution

namespace SAInterp.Res2

/-- Theorem 1.1 (p. 1), both sentences.
(a) Sherali-Adams does not polynomially simulate `Res(2)`: there is no constant `K` such that
every unsatisfiable CNF `F` with a `Res(2)` refutation of size `s` has a Sherali-Adams refutation
of size `≤ K · (s + |F|)^K + K`.
(b) There are an infinite set `I` of variable counts, unsatisfiable CNFs `F_n` over exactly the
`n` variables `Fin n` (`n ∈ I`), and constants `C`, `c > 0`, `n0` such that `|F_n| ≤ C n^C + C`,
`F_n` has a `Res(2)` refutation of size `≤ C n^C + C`, and for `n ≥ n0` every Sherali-Adams
refutation of `F_n` has size `≥ 2^{c n^{1/3}}`. -/
theorem theorem_1_1 :
    (¬ ∃ K : ℕ, ∀ (α : Type) [Fintype α] (F : CNF α) (P : List (DNF α)),
        Unsatisfiable F → IsResKRefutation 2 F P →
          ∃ π : SARefutation F, π.size ≤ K * (resKSize P + cnfSize F) ^ K + K) ∧
    (∃ (I : Set ℕ) (Fam : ∀ n : ℕ, CNF (Fin n)) (C c : ℝ) (n0 : ℕ),
        I.Infinite ∧ 0 < c ∧
        ∀ n ∈ I, Unsatisfiable (Fam n) ∧ numVars (Fam n) = n ∧
          (cnfSize (Fam n) : ℝ) ≤ C * (n : ℝ) ^ C + C ∧
          (∃ P : List (DNF (Fin n)), IsResKRefutation 2 (Fam n) P ∧
            (resKSize P : ℝ) ≤ C * (n : ℝ) ^ C + C) ∧
          (n0 ≤ n → ∀ π : SARefutation (Fam n),
            (2 : ℝ) ^ (c * (n : ℝ) ^ ((1 : ℝ) / 3)) ≤ (π.size : ℝ))) := by sorry

end SAInterp.Res2
