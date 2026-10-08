-- Prove2me | Theorems.Thm_ScatCaps_LinearSets_theorem_2_10
-- name    : ScatCaps.LinearSets.theorem_2_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:08:52.182782+00:00
-- url     : https://prove2.me/theorems/5513f88e-1d0f-4826-bdcb-487bfbdd2400
-- title:
--   Theorem 2.10, p. 16 — L_U for f(x) = x² + b x^{2^{2n+1}} is a scattered 𝔽₂-linear set of PG(2, 2^{2n}) of rank 3n
-- statement:
--   Let $n>1$, let $E=\mathbb F_{2^{6n}}$, with subfields $\mathbb F_2\subseteq\mathbb F_{2^n}\subseteq\mathbb F_{2^{2n}}$ and $\mathbb F_{2^{3n}}$. Let $b\in\mathbb F_{2^{3n}}^*$ satisfy $N_{2^{3n}/2^n}(b)\neq1$ and
--
--   $$
--   x+bx^{2^{2n+1}-1}\notin\mathbb F_{2^n}\qquad\text{for each }x\in\mathbb F_{2^{3n}}^*.
--   $$
--
--   Then for every $\omega\in\mathbb F_{2^{2n}}\setminus\mathbb F_{2^n}$ the set
--
--   $$
--   L_U=\{\langle x^2+bx^{2^{2n+1}}+x\omega\rangle_{\mathbb F_{2^{2n}}}: x\in\mathbb F_{2^{3n}}^*\}
--   $$
--
--   is a scattered $\mathbb F_2$-linear set of the projective plane $\mathrm{PG}(2,2^{2n})$ of rank $3n$.
--
--   This is the third plane family, used for Theorem 1.2 when $q=2$ and $3\mid t$.
--
--   **Formalization Note** As in the other §2 statements, $L_U$ is represented by $U=\{x^2+bx^{2^{2n+1}}+x\omega:x\in\mathbb F_{2^{3n}}\}$, rank by $|U|=2^{3n}$, and points are $\mathbb F_{2^{2n}}$-spans. The hypothesis $N_{2^{3n}/2^n}(b)\ne1$ is printed in the theorem and kept, although Proposition 2.7 does not need it. The statement is quantified over every admissible $\omega$.
-- source:
--   Bartoli, Giulietti, Marino & Polverino, Maximum scattered linear sets and complete caps in Galois spaces, arXiv:1512.07467v1, p. 16, Theorem 2.10

import Mathlib
import Definitions.Def_ScatCaps_LinearSets_Model

namespace ScatCaps.LinearSets

theorem theorem_2_10 (E : Type*) [Field E] [Fintype E]
    (n : ℕ) [ExpChar E 2] (hn : 1 < n)
    (hE : Fintype.card E = 2 ^ (6 * n))
    (b : E) (hb : b ∈ subfieldOf E 2 1 (3 * n) ∧ b ≠ 0)
    (hNb : relNorm 2 (3 * n) n b ≠ 1)
    (havoid : ∀ x : E, x ∈ subfieldOf E 2 1 (3 * n) → x ≠ 0 →
      x + b * x ^ (2 ^ (2 * n + 1) - 1) ∉ subfieldOf E 2 1 n)
    (ω : E) (hω : ω ∈ subfieldOf E 2 1 (2 * n) ∧ ω ∉ subfieldOf E 2 1 n) :
    IsFqSubspace (subfieldOf E 2 1 1)
      (sec2Set (subfieldOf E 2 1 (3 * n)) (binom 2 n 1 1 b) ω) ∧
    HasRank (subfieldOf E 2 1 1)
      (sec2Set (subfieldOf E 2 1 (3 * n)) (binom 2 n 1 1 b) ω) (3 * n) ∧
    IsScattered (subfieldOf E 2 1 1) (subfieldOf E 2 1 (2 * n))
      (sec2Set (subfieldOf E 2 1 (3 * n)) (binom 2 n 1 1 b) ω) := by sorry

end ScatCaps.LinearSets
