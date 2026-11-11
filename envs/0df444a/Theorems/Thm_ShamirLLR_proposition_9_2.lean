-- Prove2me | Theorems.Thm_ShamirLLR_proposition_9_2
-- name    : ShamirLLR.proposition_9_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T08:28:35.800284+00:00
-- url     : https://prove2.me/theorems/97d0ae3d-8128-4d39-8943-ed5cb3affa53
-- title:
--   Proposition 9.2 — structured leakage with base $2/\pi$
-- statement:
--   Fix the data $\mathcal N, D, Q$ defining $G_{p,3}$ (a nonempty finite collection of degree-two filtered nilmanifolds, $D\ge1$ bounding their dimensions, $Q\ge1$) and $0<b<1$. There are constants $A,C>0$, depending only on these data and $b$, such that for all sufficiently large $m$, every integer $bm\le r<m$, and every odd prime $p$ with $\log p\ge Cm^2\log(2m)$,
--   $$
--   \mathbb E_{a\in\mathcal A_{p,m}}\Delta_{G_{p,3}}(a;r)\le A\Bigl(\frac2\pi\Bigr)^{r}.
--   $$
--   The supremum over the leakage maps is inside the expectation.
--
--   This structured estimate is the input of the outer reduction in the proof of Theorem 1.
--
--   Differences from the source:
--   - encoding: "for all sufficiently large $m$" → $m\ge m_0$ with $m_0>0$ chosen together with $A, C$; reason: same quantifier order
--   - encoding: the class data of §4.1 → hypotheses: $\mathcal N$ a finite nonempty set of `LSS.Nilmanifold 2`, $D\ge1$ with all dimensions $\le D$, $Q\ge1$; $G_{p,3}$ is `classG p N D Q`; reason: §4.1 and Definition 4.1
-- source:
--   Hwang–Maji–Shkredov–Ye, Local Leakage Resilience of Multiplication-friendly Shamir Secret Sharing (manuscript, 2 Nov 2026; held version, sha256 fcd6871f…), Proposition 9.2, Eq. (73), p.64, under the hypotheses of Lemma 7.1, p.46 (PDF pp.65, 47)

import Mathlib
import Definitions.Def_LSSNil
import Definitions.Def_ShamirLLR_evalTuples
import Definitions.Def_ShamirLLR_deltaClass
import Definitions.Def_ShamirLLR_classG

set_option autoImplicit false

namespace ShamirLLR

/-- **Proposition 9.2 (Structured leakage with base `2/π`).** Under the hypotheses of Lemma 7.1:
fix the data `N, D, Q` defining `G_{p,3}` and `0 < b < 1`. There are constants `A, C > 0`,
depending only on these data and `b`, such that for all sufficiently large `m`, every integer
`bm ≤ r < m`, and every odd prime `p` with `log p ≥ C m² log(2m)`,
`𝔼_{a ∈ A_{p,m}} Δ_{G_{p,3}}(a; r) ≤ A (2/π)^r`, the supremum over the maps being inside the
expectation.

Source: Hwang–Maji–Shkredov–Ye, manuscript of 2 Nov 2026 (held version, sha256 fcd6871f…),
Proposition 9.2, Eq. (73), p.64; the hypotheses of Lemma 7.1, p.46.

**Formalization Note.** `N` is a nonempty finite set of `LSS.Nilmanifold 2`, `D ≥ 1` bounds their
dimensions, `Q ≥ 1` (§4.1, p.24); `G_{p,3}` is `classG p N D Q`. "Sufficiently large m" is
`m ≥ m₀` with `m₀` chosen with `A, C`. Natural log. -/
theorem proposition_9_2 (N : Set (LSS.Nilmanifold 2)) (hNfin : N.Finite) (hNne : N.Nonempty)
    (D : ℕ) (hD : 1 ≤ D) (hND : ∀ G ∈ N, G.d ≤ D) (Q : ℝ) (hQ : 1 ≤ Q) (b : ℝ) (hb0 : 0 < b)
    (hb1 : b < 1) :
    ∃ A C m₀ : ℝ, 0 < A ∧ 0 < C ∧ 0 < m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∀ r : ℕ, b * m ≤ r → r < m →
      ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → C * (m : ℝ) ^ 2 * Real.log (2 * m) ≤ Real.log p →
        avgTuples p m (fun a => deltaClass (classG p N D Q) a r) ≤ A * (2 / Real.pi) ^ r := by sorry

end ShamirLLR
