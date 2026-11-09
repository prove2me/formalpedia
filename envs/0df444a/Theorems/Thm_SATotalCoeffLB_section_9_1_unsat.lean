-- Prove2me | Theorems.Thm_SATotalCoeffLB_section_9_1_unsat
-- name    : SATotalCoeffLB.section_9_1_unsat
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:21:11.013815+00:00
-- url     : https://prove2.me/theorems/553e71c8-04e4-4abd-9ad0-ae8266ff2de3
-- title:
--   Section 9.1 — the system $P_{H,s}$ is unsatisfiable
-- statement:
--   Let $E \subseteq \binom{[n]}{2}$, $H \in \mathbb F_2^{t\times E}$ and signs $s \in \{\pm1\}^E$ satisfy (27) for the code $C = \ker H$: no $\bar x \in \mathbb F_2^n$ has $(-1)^{a_z(\bar x)} = s^z$ for every $z \in C$. Then the system
--
--   $$
--   P_{H,s} = \{p_{ij} : 1 \le i < j \le n\} \cup \{q_e : e \in E\}, \qquad q_e = \frac{1 - s_e Y_e T^{H_{\cdot,e}}}{2},
--   $$
--
--   has no common zero: no $\pm1$ assignment to $X, Y, T$ makes every AND check and every parity check vanish.
--
--   This is item 1's unsatisfiability clause of Theorem 3 for the constructed system.
--
--   Differences from the source:
--   - generalization: $H$ the parity-check matrix of Lemma 15 on the graph of Section 9.1 and $s$ the signs chosen in (27) → any $E$, any $H \in \mathbb F_2^{t\times E}$ and any $\pm1$ signs $s$ satisfying (27) for $C = \ker H$; reason: the page's argument uses only (27)
--   - encoding: signs $s_e \in \{\pm 1\}$ → real numbers with $s_e = 1 \lor s_e = -1$; reason: same values
--   - encoding: a $\pm1$ assignment to $X, Y, T$ → a bit vector $x$, variable $v$ taking the value $(-1)^{x_v}$; reason: the $\{\pm1\}$ encoding; same assignments
-- source:
--   Chen–Jin, Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for Sherali–Adams, STOC 2027 submission (manuscript sha256 da19ece6…9d9178), Section 9.1, p.52

import Mathlib
import Definitions.Def_SATotalCoeffLB_andCheck
import Definitions.Def_SATotalCoeffLB_parityCheckH
import Definitions.Def_SATotalCoeffLB_QForm_eval
import Definitions.Def_SATotalCoeffLB_formOf
import Definitions.Def_SATotalCoeffLB_signProd

namespace SATotalCoeffLB

/-- **Section 9.1, unsatisfiability of `P_{H,s}`**, p.52 of Chen–Jin, *Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for
Sherali–Adams*, STOC 2027 submission manuscript
(sha256 da19ece6898e20b159d01408327de710d69219772cc1f088c80301a6679d9178).

Let `E` be a set of pairs on `[n]`, `H ∈ F₂^{t×E}`, and `s ∈ {±1}^E` signs satisfying (27) for the
code `C = ker H`: no `x̄ ∈ F₂ⁿ` has `(−1)^{a_z(x̄)} = s^z` for every `z ∈ C`. Then the system
`P_{H,s}` — the AND checks `p_ij` for **all** pairs `i < j` and the parity checks `q_e` of Eq. (24)
for `e ∈ E` — has no common zero on the Boolean cube in the variables `X, Y, T`. -/
theorem section_9_1_unsat (n t : ℕ) (E : Finset (Pair n)) (H : Matrix (Fin t) E (ZMod 2))
    (s : E → ℝ) (hs : ∀ e, s e = 1 ∨ s e = -1)
    (h27 : ¬ ∃ xb : Fin n → ZMod 2, ∀ z : E → ZMod 2, H.mulVec z = 0 →
      (-1 : ℝ) ^ ((formOf E z).eval xb).val = signProd s z) :
    ¬ ∃ x : Var n t → ZMod 2,
      (∀ e : Pair n, andCheck t e x = 0) ∧ ∀ e : E, parityCheckH H s e x = 0 := by sorry

end SATotalCoeffLB
