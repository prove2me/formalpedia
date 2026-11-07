-- Prove2me | Theorems.Thm_SYKEdge_fact_3_7_moments
-- name    : SYKEdge.fact_3_7_moments
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:06:36.529907+00:00
-- url     : https://prove2.me/theorems/ef065824-b7fa-43bf-897a-41e42219da89
-- title:
--   Fact 3.7, moment clause — $\|f(g)-\mathbb Ef(g)\|_p\le O(\sigma\sqrt p)$ for $\sigma$-Lipschitz $f$
-- statement:
--   Let $f:\mathbb R^m\to\mathbb R$ be $\sigma$-Lipschitz, $|f(x)-f(y)|\le\sigma\|x-y\|_2$, and $X=f(g)-\mathbb E_gf(g)$ with $g\sim N(0,\mathrm{Id}_m)$. Then for every $p\ge2$
--   $$\|X\|_p=\big(\mathbb E|X|^p\big)^{1/p}\le C\,\sigma\sqrt p$$
--   for an absolute constant $C$.
--
--   This is the moment form of Gaussian concentration (Vershynin, HDP); the tail form is the published theorem `HighDimStat.TailBounds.lipschitz_gaussian_concentration`. The paper applies it with $p=L+1$ in Lemma 4.18.
--
--   **Formalization Note** $p$ is real; $\|x-y\|_2$ is the Euclidean norm on $\mathbb R^m$.
--
--   Differences from the source:
--   - encoding: O(1) in ‖X‖_p ⩽ O(σ√p) → one absolute constant C > 0 quantified before m, σ, f and p; reason: Fact 3.7's O(·) hides an absolute constant (the moment bound of a sub-Gaussian variable); it depends on none of m, σ, f, p
--   - encoding: σ-Lipschitz → 0 ⩽ σ and |f x − f y| ⩽ σ‖x − y‖₂ for all x, y; reason: a Lipschitz constant is nonnegative (only m = 0 would allow σ < 0)
-- source:
--   Basu, Kothari, Midha, Sharp Bounds on Ground State Energy of the SYK Model, arXiv:2607.27185v2, Fact 3.7, last sentence, p.18

import Mathlib
import Definitions.Def_SYKEdge_Hamiltonian
open MeasureTheory

namespace SYKEdge

/-- **Fact 3.7**, moment clause (Concentration of Lipschitz Functions [Ver18]), A. Basu, P. K. Kothari, S. Midha, *Sharp Bounds on Ground State Energy of the SYK Model*,
arXiv:2607.27185v2, p.18.

Let `f : ℝ^m → ℝ` be `σ`-Lipschitz, `|f(x) − f(y)| ⩽ σ‖x − y‖₂`, and `X := f(g) − E_g f(g)` for
`g ∼ N(0, Id_m)`. In particular, for every `p ⩾ 2`, `‖X‖_p ⩽ O(σ√p)`.

**Formalization Note.** `O(1)` is an absolute constant `C > 0` chosen before `m`, `σ`, `f` and `p`;
`‖X‖_p = (E|X|^p)^{1/p}` and `p` is real. `σ ⩾ 0` is the Lipschitz constant. The tail clause of
Fact 3.7 is the published theorem `HighDimStat.TailBounds.lipschitz_gaussian_concentration`. -/
theorem fact_3_7_moments :
    ∃ C : ℝ, 0 < C ∧
      ∀ (m : ℕ) (σ : ℝ) (f : (Fin m → ℝ) → ℝ), 0 ≤ σ →
        (∀ x y : Fin m → ℝ, |f x - f y| ≤ σ * Real.sqrt (∑ i, (x i - y i) ^ 2)) →
        ∀ p : ℝ, 2 ≤ p →
          (∫ g, |f g - ∫ g', f g' ∂stdGauss (Fin m)| ^ p ∂stdGauss (Fin m)) ^ (1 / p) ≤
            C * σ * Real.sqrt p := by sorry

end SYKEdge
