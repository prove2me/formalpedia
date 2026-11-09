-- Prove2me | Theorems.Thm_SATotalCoeffLB_section_9_1_choice_of_s
-- name    : SATotalCoeffLB.section_9_1_choice_of_s
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:20:52.607837+00:00
-- url     : https://prove2.me/theorems/88c64ae4-8734-4fdf-a401-93102301273e
-- title:
--   Section 9.1, Eq. (27) — signs $s$ with no $\bar x$ satisfying $(-1)^{a_z(\bar x)} = s^z$ on $C$
-- statement:
--   Let $E \subseteq \binom{[n]}{2}$ and let $C \subseteq \mathbb F_2^E$ be a linear code of dimension $d > n$. Then there are signs $s = (s_e)_{e \in E} \in \{\pm1\}^E$ such that
--
--   $$
--   \text{there is no } \bar x \in \mathbb F_2^n \text{ with } (-1)^{a_z(\bar x)} = s^z \text{ for every } z \in C, \tag{27}
--   $$
--
--   where $s^z = \prod_{e \in E : z_e = 1} s_e$.
--
--   On the page: there are $2^d$ homomorphisms $(C, +) \to (\{\pm1\}, \cdot)$ but at most $2^n$ of them have the form $z \mapsto (-1)^{a_z(\bar x)}$; a homomorphism outside this set, extended to $\mathbb F_2^E$, has the form $z \mapsto s^z$. These signs make the system $P_{H,s}$ unsatisfiable.
--
--   Differences from the source:
--   - generalization: $C$ the code of Lemma 15, with $d = \dim C \ge m/3 > n$ for sufficiently large $m$ → any linear code $C \subseteq \mathbb F_2^E$ with $\dim C > n$; reason: the counting argument uses only $d > n$; the page's code satisfies it
--   - encoding: signs $s_e \in \{\pm 1\}$ → real numbers with $s_e = 1 \lor s_e = -1$; reason: same values
--   - encoding: $(-1)^{a_z(\bar x)}$ with $a_z(\bar x) \in \mathbb F_2$ → $(-1)^{\mathrm{val}(a_z(\bar x))}$, `val` the representative in $\{0,1\}$; reason: same value
-- source:
--   Chen–Jin, Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for Sherali–Adams, STOC 2027 submission (manuscript sha256 da19ece6…9d9178), Section 9.1, Choice of s, pp.51–52, Eq. (27)

import Mathlib
import Definitions.Def_SATotalCoeffLB_QForm_eval
import Definitions.Def_SATotalCoeffLB_formOf
import Definitions.Def_SATotalCoeffLB_signProd

namespace SATotalCoeffLB

/-- **Section 9.1, choice of `s` (Eq. (27))**, pp.51–52 of Chen–Jin, *Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for
Sherali–Adams*, STOC 2027 submission manuscript
(sha256 da19ece6898e20b159d01408327de710d69219772cc1f088c80301a6679d9178).

Let `E` be a set of pairs on `[n]` and `C ⊆ F₂^E` a linear code of dimension `d > n`. Then there are
signs `s = (s_e)_{e∈E} ∈ {±1}^E` such that there is no `x̄ ∈ F₂ⁿ` with
`(−1)^{a_z(x̄)} = s^z` for every `z ∈ C`, where `s^z = ∏_{e : z_e = 1} s_e` (Eq. (27)).

**Formalization Note** The page obtains `d = dim C ≥ m/3 > n` for sufficiently large `m`; the
statement takes `n < dim C` as its hypothesis. Signs are reals equal to `1` or `-1`. -/
theorem section_9_1_choice_of_s (n : ℕ) (E : Finset (Pair n))
    (C : Submodule (ZMod 2) (E → ZMod 2)) (hd : n < Module.finrank (ZMod 2) C) :
    ∃ s : E → ℝ, (∀ e, s e = 1 ∨ s e = -1) ∧
      ¬ ∃ xb : Fin n → ZMod 2, ∀ z ∈ C,
        (-1 : ℝ) ^ ((formOf E z).eval xb).val = signProd s z := by sorry

end SATotalCoeffLB
