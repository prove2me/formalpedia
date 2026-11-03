-- Prove2me | Theorems.Thm_ProxFlatIP_theorem_5
-- name    : ProxFlatIP.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:14:33.479562+00:00
-- url     : https://prove2.me/theorems/9a05351b-38f0-4ce7-be22-fbb1e0ea0ebe
-- title:
--   Theorem 5 (strengthened: one $z^*$ for every $\alpha$) — $|\alpha^\top(x^*-z^*)|<\frac{4n+2}{9}\Delta^\alpha(A)$
-- statement:
--   Let $A\in\mathbb Z^{m\times n}$ have full column rank, $n\ge2$, $b\in\mathbb Z^m$, $c\in\mathbb Q^n$. Let $x^*$ be an optimal vertex of $\mathrm{LP}(A,b,c)$. If $\mathrm{IP}(A,b,c)$ is feasible, then there exists an optimal solution $z^*$ such that for every $\alpha\in\mathbb Z^n\setminus\{0\}$,
--   $$|\alpha^\top(x^*-z^*)|<\frac{4n+2}{9}\cdot\Delta^\alpha(A).$$
--
--   This is the general form behind the proximity theorem: it bounds every integral linear form of $x^*-z^*$ in terms of the data of that form.
--
--   Differences from the source:
--   - generalization: for each α there is an optimal z* → one optimal z* for all α; reason: the proof chooses z* by Lemma 8 before α enters, Theorem 2 needs one z* for all ±eᵢ, and the uniform form implies the printed one
-- source:
--   Celaya, Kuhlmann, Paat, Weismantel, Proximity and flatness bounds for linear integer optimization, arXiv:2211.14941v1 [math.OC] (preprint, 27 Nov 2022), https://arxiv.org/abs/2211.14941v1, Theorem 5, p.3

import Mathlib
import Definitions.Def_ProxFlatIP_Minors

open Matrix

namespace ProxFlatIP

/-- **Theorem 5** (strengthened: one `z*` for every `α`) (arXiv:2211.14941v1, Theorem 5, p.3). Let
`n ≥ 2`, `b ∈ ℤᵐ`, `c ∈ ℚⁿ`, and let `x*` be an optimal vertex of `LP(A,b,c)`. If `IP(A,b,c)` is
feasible, there is an optimal solution `z*` such that `|α⊤(x* − z*)| < ((4n+2)/9) Δ^α(A)` for every
`α ∈ ℤⁿ \ {0}`.

**Formalization Note.** The paper fixes `α` first, so its `z*` may depend on `α`. Its proof chooses
`z*` through Lemma 8 before `α` enters, and Theorem 2 needs the uniform form. The uniform form implies
the printed one. -/
theorem theorem_5 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (hA : FullColRank A) (hn : 2 ≤ n)
    (b : Fin m → ℤ) (c : Fin n → ℚ) (xs : Fin n → ℝ) (hxs : IsLPOptimalVertex A b c xs)
    (hIP : IsIPFeasible A b) :
    ∃ zs : Fin n → ℝ, IsIPOptimal A b c zs ∧
      ∀ α : Fin n → ℤ, α ≠ 0 →
        |castVec α ⬝ᵥ (xs - zs)| < (4 * (n : ℝ) + 2) / 9 * (deltaAlpha A α : ℝ) := by sorry

end ProxFlatIP
