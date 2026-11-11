-- Prove2me | Theorems.Thm_PermInvCC_lemma_C_1
-- name    : PermInvCC.lemma_C_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:23:07.986985+00:00
-- url     : https://prove2.me/theorems/db93b75e-f79c-454a-8e51-daab4afe1def
-- title:
--   Lemma C.1 — Nayak–Wu degree lower bound
-- statement:
--   There is an absolute constant $c_{NW}>0$ such that the following holds. Let $L\ge1$ and $0\le r<s\le L$ be integers. Suppose a real polynomial $A$ in $L$ variables satisfies
--   $$-\tfrac13\le A(w)\le\tfrac43\quad(w\in\{0,1\}^L),$$
--   $|A(w)|\le\tfrac13$ when $|w|=r$, and $|A(w)-1|\le\tfrac13$ when $|w|=s$. Choose $u\in\{r,s\}$ maximizing $|u-L/2|$. Then
--   $$\deg A\ge c_{NW}\Bigl(\sqrt{\frac{L}{s-r}}+\frac{\sqrt{u(L-u)}}{s-r}\Bigr).$$
--
--   It is the input to the adjacent-integer degree bound, Lemma 4.2.
--
--   **Formalization Note** $\deg$ is the total degree and $|w|$ the number of ones.
--
--   Differences from the source:
--   - encoding: choose u ∈ {r, s} maximizing |u − L/2| → u = r if |r − L/2| ≥ |s − L/2|, else s; reason: on a tie r + s = L and both choices give the same u(L − u)
-- source:
--   Huang and Ye, Quantum Advantage of Permutation-Invariant Functions in Communication Complexity, arXiv:2609.40116 (held version, sha256 fe1797dd…), Lemma C.1, p.47

import Mathlib

namespace PermInvCC

/-- **Lemma C.1 (Polynomial Degree Lower Bound, [NW99, Theorem 1.1])** (Y. Huang and Z. Ye,
arXiv:2609.40116, held version sha256 fe1797dd…, p.47). Let `L ≥ 1` and `0 ≤ r < s ≤ L` be
integers. Suppose a real polynomial `A` in `L` variables satisfies `−1/3 ≤ A(w) ≤ 4/3` on
`{0, 1}^L`, `|A(w)| ≤ 1/3` when `|w| = r` and `|A(w) − 1| ≤ 1/3` when `|w| = s`. Choose
`u ∈ {r, s}` maximizing `|u − L/2|`. Then, for an absolute constant `c_NW > 0`,
`deg A ≥ c_NW (√(L/(s − r)) + √(u(L − u))/(s − r))`.

**Formalization Note.** `deg` is the total degree; points of `{0, 1}^L` are `w : Fin L → Bool`
evaluated as `0/1` vectors, `|w|` the number of ones. `u` is `r` when `|r − L/2| ≥ |s − L/2|`
and `s` otherwise; on a tie `r + s = L`, and both choices give the same `u(L − u)`. -/
theorem lemma_C_1 :
    ∃ c : ℝ, 0 < c ∧ ∀ (L r s : ℕ), 1 ≤ L → r < s → s ≤ L →
      ∀ A : MvPolynomial (Fin L) ℝ,
        (∀ w : Fin L → Bool,
          -(1 / 3 : ℝ) ≤ MvPolynomial.eval (fun i => if w i then (1 : ℝ) else 0) A ∧
          MvPolynomial.eval (fun i => if w i then (1 : ℝ) else 0) A ≤ 4 / 3) →
        (∀ w : Fin L → Bool, (Finset.univ.filter fun i => w i).card = r →
          |MvPolynomial.eval (fun i => if w i then (1 : ℝ) else 0) A| ≤ 1 / 3) →
        (∀ w : Fin L → Bool, (Finset.univ.filter fun i => w i).card = s →
          |MvPolynomial.eval (fun i => if w i then (1 : ℝ) else 0) A - 1| ≤ 1 / 3) →
        let u : ℕ := if |(r : ℝ) - L / 2| ≥ |(s : ℝ) - L / 2| then r else s
        c * (Real.sqrt ((L : ℝ) / ((s : ℝ) - r)) +
            Real.sqrt ((u : ℝ) * ((L : ℝ) - u)) / ((s : ℝ) - r)) ≤ A.totalDegree := by sorry

end PermInvCC
