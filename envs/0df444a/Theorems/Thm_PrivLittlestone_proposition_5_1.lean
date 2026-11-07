-- Prove2me | Theorems.Thm_PrivLittlestone_proposition_5_1
-- name    : PrivLittlestone.proposition_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:30:34.005014+00:00
-- url     : https://prove2.me/theorems/e97907be-8aa5-4237-a259-26cee6597644
-- title:
--   Proposition 5.1 — every Littlestone class of dimension $d$ has a ranked candidate system with $D = d$, $B = 4(d+1)$, coverage and $|C(\emptyset)| \le 2[2(d+1)]^d$
-- statement:
--   For every nonempty binary class $H$ of Littlestone dimension $d \ge 1$ there are a fixed universe $U \supseteq H$, a rank $\rho : U \to \{0, \dots, d\}$ and finite nonempty candidate sets $C(S) \subseteq U$ such that:
--
--   1. with the binary loss $\ell_{(x,y)}(h) = \mathbf 1\{h(x) \neq y\}$, this is a ranked candidate system with $D = d$ and $B = 4(d+1)$;
--   2. for every finite sample $S$ and every $h \in U$, some $g \in C(S)$ agrees with $h$ at every instance occurring in $S$;
--   3. $|C(\emptyset)| \le 2[2(d+1)]^d$.
--
--   This is the interface between the Moran–Yan construction and the continual learner: with it, Theorem 4.1 applies to every Littlestone class.
--
--   **Formalization Note** Candidates are elements of $X \to \{0,1\}$ and the universe is a set of them containing every $C(S)$; records are labeled examples.
--
--   Differences from the source:
--
--   - encoding: a universe U ⊇ H with ρ : U → {0, …, d} and C(S) ⊆ U → a set U of classifiers containing H and every C(S), with ρ defined on all classifiers and bounded by d; reason: only the values on U are used
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), Proposition 5.1, p.9 (construction in Appendix A.2, pp.17–19)

import Mathlib
import Definitions.Def_PrivLittlestone_RankedCandidateSystem
import Definitions.Def_UnderstandingML_Online

namespace PrivLittlestone

/-- **Proposition 5.1 (Imported Littlestone candidate system)** (He–He, *Private Online Learning
of Littlestone Classes and Matroid Flats*, STOC 2027 submission manuscript (sha256
21480556…c562), Proposition 5.1, p.9; construction and verification in Appendix A.2,
pp.17–19). For every nonempty binary class `H` of Littlestone dimension `d ≥ 1`, there are a fixed
universe `U ⊇ H`, a rank `ρ : U → {0, …, d}`, and finite nonempty candidate sets `C(S) ⊆ U` such
that:
1. with `ℓ_{(x,y)}(h) = 1{h(x) ≠ y}`, this is a ranked candidate system with `D = d` and
   `B = 4(d + 1)`;
2. for every finite `S` and every `h ∈ U`, some `g ∈ C(S)` agrees with `h` at every instance
   occurring in `S`;
3. `|C(∅)| ≤ 2[2(d + 1)]^d`.

**Formalization Note** Candidates are elements of `X → Bool`; the universe `U` is a set of them
containing every `C(S)`. Records are labeled examples `(x, y) ∈ X × Bool`. -/
theorem proposition_5_1 {X : Type*} (H : Set (X → Bool)) (d : ℕ) (hH : H.Nonempty)
    (hd : UnderstandingML.ldim H = d) (hd1 : 1 ≤ d) :
    ∃ Uu : Set (X → Bool), H ⊆ Uu ∧
      ∃ sys : RankedCandidateSystem (X × Bool) (X → Bool) d (4 * ((d : ℝ) + 1)),
        (∀ S : List (X × Bool), ∀ g ∈ sys.C S, g ∈ Uu) ∧
        (∀ (u : X × Bool) (h : X → Bool), sys.loss u h = if h u.1 ≠ u.2 then 1 else 0) ∧
        (∀ S : List (X × Bool), ∀ h ∈ Uu, ∃ g ∈ sys.C S, ∀ u ∈ S, g u.1 = h u.1) ∧
        (((sys.C []).card : ℕ) : ℝ) ≤ 2 * (2 * ((d : ℝ) + 1)) ^ d := by sorry

end PrivLittlestone
