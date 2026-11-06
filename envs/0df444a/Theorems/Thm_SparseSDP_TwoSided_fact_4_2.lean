-- Prove2me | Theorems.Thm_SparseSDP_TwoSided_fact_4_2
-- name    : SparseSDP.TwoSided.fact_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:56:35.970534+00:00
-- url     : https://prove2.me/theorems/7d8ed770-377b-4960-9026-419d7ff2b557
-- title:
--   Fact 4.2, p. 26, in the form (252)–(253), p. 50 — random-start Lánczos
-- statement:
--   There is a universal constant $C_0$ with the following property. Let $K$ be real symmetric of size $d$, $u\sim\mathrm{Unif}(S^{d-1})$, $\zeta,\eta\in(0,1/2)$, $\Gamma=\log(\sqrt d/(\zeta\eta))$, and let $q\le d$ satisfy $q\ge\min\{d,\lceil C_0\sqrt{\Gamma\max\{\|K\|,\Gamma\}}\rceil\}$. Then
--   $$
--   \|\text{LánczosExp}(K,u,q)-e^Ku\|_2\le\zeta\|e^Ku\|_2
--   $$
--   with probability at least $1-\eta$. If a product by $K$ costs $T_K$, the cost of the program is $O(q(T_K+d)+q^2)$.
--
--   The paper imports this from Carmon, Duchi, Sidford and Tian [CDST19, Corollary 20, Proposition 23].
--
--   Differences from the source:
--   - reading: $q=\tilde O(\sqrt{\max\{1,\|K\|\}})$ capped at $n$; $\Gamma=\Theta(\log(\sqrt n/(\zeta\eta)))$ → every $q\le d$ above $\min\{d,\lceil C_0\sqrt{\Gamma\max\{\|K\|,\Gamma\}}\rceil\}$ with $\Gamma$ exactly that logarithm; reason: Eq. (252) is the paper's own quantitative form; the constant $C_0$ absorbs the $\Theta$
--   - encoding: $u\sim\mathrm{Unif}(S^{n-1})$ → `sphereLaw`, the law of normalized Gaussians; reason: its standard construction
--   - encoding: with probability at least $1-p$ → the failure set has outer measure at most $p$ under `tapeLaw`; reason: no measurability of the event needs assuming; for a measurable event it is the same statement
-- source:
--   Brandão, Dalzell, Gilyén, Vasconcelos, Solving Sparse SDPs in Sublinear Time, arXiv:2609.40302, Fact 4.2, p. 26, Eq. (90); Eqs. (252), (253), p. 50

import Mathlib
import Definitions.Def_SparseSDP_TwoSided_lanczosProg
import Definitions.Def_SparseSDP_TwoSided_sphereLaw

open Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator

namespace SparseSDP.TwoSided

/-- **Fact 4.2** (Uniform Random Real Lánczos), p. 26, in the form (252)–(253), p. 50.

Brandão, Dalzell, Gilyén, Vasconcelos, *Solving Sparse SDPs in Sublinear Time*, arXiv:2609.40302,
Fact 4.2, p. 26; Eqs. (252), (253), p. 50. Imported by the paper from [CDST19, Corollary 20,
Proposition 23].

Any budget `q` with `min{d, ⌈C₀ √(Γ max{‖K‖, Γ})⌉} ≤ q ≤ d`, `Γ = log(√d/(ζη))`, gives (90) with
probability at least `1 − η`. The cost clause is `O(q(T_K + d) + q²)` on every tape. -/
theorem fact_4_2 : ∃ C₀ : ℝ, 0 < C₀ ∧
    ∀ (d : ℕ) (K : Mat d) (ζ η : ℝ) (q : ℕ), 1 ≤ d → K.IsHermitian →
      0 < ζ → ζ < 1 / 2 → 0 < η → η < 1 / 2 →
      min d ⌈C₀ * √(Real.log (√(d : ℝ) / (ζ * η)) *
        max ‖K‖ (Real.log (√(d : ℝ) / (ζ * η))))⌉₊ ≤ q → q ≤ d →
      (sphereLaw d {u | ¬ l2 (lanczosExp K u q - expM K *ᵥ u) ≤ ζ * l2 (expM K *ᵥ u)} ≤
        ENNReal.ofReal η) ∧
      ∀ (mv : Vec d → Prog (Vec d)) (TK : ℝ) (u : Vec d) (tape : Tape), 0 ≤ TK →
        Implements mv K TK →
        (runCost (lanczosProg mv u q) tape : ℝ) ≤ C₀ * ((q : ℝ) * (TK + d) + (q : ℝ) ^ 2) := by sorry

end SparseSDP.TwoSided
