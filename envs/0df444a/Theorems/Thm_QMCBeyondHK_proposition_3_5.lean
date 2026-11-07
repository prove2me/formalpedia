-- Prove2me | Theorems.Thm_QMCBeyondHK_proposition_3_5
-- name    : QMCBeyondHK.proposition_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:36:49.211184+00:00
-- url     : https://prove2.me/theorems/3a012120-9f51-4fd9-9068-b6171144e33a
-- title:
--   Proposition 3.5 — error decomposition: $\mathrm{err}(A,g)^2 \le 2\,\mathrm{err}(A,\Pi_{\le\ell}g)^2 + 2\,\mathrm{err}(A,\Pi_{>\ell}g)^2$
-- statement:
--   Let $d \ge 1$, $n \ge 1$, $\ell = \lceil 10\log_2 n\rceil$. For every $g \in L^2([0,1)^d)$ and every finite point set $A \subset [0,1)^d$ with $|A| = m \ge 1$,
--   $$
--   \operatorname{err}(A, g)^2 \le 2\, \operatorname{err}(A, \Pi_{\le\ell}\, g)^2 + 2\, \operatorname{err}(A, \Pi_{>\ell}\, g)^2 .
--   $$
--
--   It splits the integration error into a low-order part, controlled by the uncorrelated discrepancies, and a high-order part, controlled by the orthogonality of increments.
--
--   Differences from the source:
--   - generalization: a finite set A ⊂ [0,1)^d → a tuple of m ≥ 1 points of [0,1)^d, repetitions allowed; reason: a finite set of m points is a tuple without repetitions
--   - encoding: A finite → A nonempty (m ≥ 1); reason: err(A, g) involves |A|⁻¹ and is undefined for the empty set
--   - encoding: Π>ℓ g, the orthogonal projection onto the span of the remaining non-constant Haar functions → the pointwise function g − ḡ − Π≤ℓ g; reason: the Haar functions form an orthogonal basis, so this is that projection, as an everywhere-defined representative
--   - encoding: g ∈ L²([0,1)^d) → a measurable g : ℝ^d → ℝ with MemLp g 2 on the cube; reason: a measurable representative is needed to evaluate g at sample points; values off the cube are never used
-- source:
--   Ezeunala, Jha, Jiang, Quasi-Monte Carlo Beyond Hardy–Krause II: (1 + ε)n Samples Suffice, arXiv:2609.10921 (sha256 bc273e88…), Proposition 3.5, p.13 (PDF p.15)

import Mathlib
import Definitions.Def_QMCBeyondHK_lowOrder

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace QMCBeyondHK

/-- Proposition 3.5 (Error decomposition), printed p.13 (PDF p.15) of arXiv:2609.10921
(sha256 bc273e88…): for every `g ∈ L²([0,1)^d)` and every finite set `A ⊂ [0,1)^d`,
`err(A, g)² ≤ 2 err(A, Π≤ℓ g)² + 2 err(A, Π>ℓ g)²`.

**Formalization Note** `A` is a nonempty tuple of `m ≥ 1` points of the cube; `ℓ = ⌈10 log₂ n⌉`;
`Π>ℓ g` is the pointwise representative `g − ḡ − Π≤ℓ g`. -/
theorem proposition_3_5 (d : ℕ) (hd : 1 ≤ d) (n : ℕ) (hn : 1 ≤ n) (g : (Fin d → ℝ) → ℝ)
    (hg : Measurable g) (hg2 : MemLp g 2 (unif d)) (m : ℕ) (hm : 1 ≤ m)
    (A : Fin m → Fin d → ℝ) (hA : ∀ t, A t ∈ cube d) :
    err A g ^ 2 ≤ 2 * err A (lowProj d (ell n) g) ^ 2 + 2 * err A (highProj d (ell n) g) ^ 2 := by sorry

end QMCBeyondHK
