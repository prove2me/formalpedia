-- Prove2me | Theorems.Thm_TeschlODE_Horseshoe_shift_periodicPts_countable_dense
-- name    : TeschlODE.Horseshoe.shift_periodicPts_countable_dense
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T06:08:03.612749+00:00
-- url     : https://prove2.me/theorems/ec92f229-3c9d-4923-bc36-70e84ec452bd
-- title:
--   Lemma 11.8 — the shift on $\Sigma_N$ has countably many periodic points, and they are dense
-- statement:
--   Let $N \ge 2$ and let $\sigma$ be the shift on the one-sided space $\Sigma_N = \{0, \dots, N-1\}^{\mathbb{N}_0}$ with the metric $d(x,y) = \sum_n |x_n - y_n|/N^n$ (11.28). Then the set of periodic points
--   $$\mathrm{Per}(\sigma) = \{x \in \Sigma_N : \sigma^n(x) = x \text{ for some } n \ge 1\}$$
--   is countable, and it is dense: for every $x \in \Sigma_N$ and $\varepsilon > 0$ there is $p \in \mathrm{Per}(\sigma)$ with $d(p, x) < \varepsilon$.
--   Together with Lemma 11.9 this makes the full shift chaotic. The book notes that the same holds for the two-sided shift of the horseshoe, and that is the "in particular it is chaotic" part of Theorem 13.1.
--
--   **Formalization Note.** Density is stated in $\varepsilon$–$\delta$ form with the book's metric (11.28), which is a function here, not an instance.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 303, Lemma 11.8

import Mathlib
import Definitions.Def_TeschlODE_Shared_shift
import Definitions.Def_TeschlODE_Shared_symDist

namespace TeschlODE.Horseshoe

/-- Teschl, Lemma 11.8, p. 303: the shift map `σ` on the one-sided space `Σ_N` (`N ≥ 2`) has a
countable number of periodic points (`{x | σⁿ(x) = x for some n ≥ 1}`), and they are dense with
respect to the metric (11.28): every `x ∈ Σ_N` is within any `ε > 0` of a periodic point. -/
theorem shift_periodicPts_countable_dense (N : ℕ) (hN : 2 ≤ N) :
    (Function.periodicPts (TeschlODE.Shared.shift (N := N))).Countable ∧
      ∀ x : ℕ → Fin N, ∀ ε : ℝ, 0 < ε →
        ∃ p ∈ Function.periodicPts (TeschlODE.Shared.shift (N := N)), TeschlODE.Shared.symDist N p x < ε := by sorry

end TeschlODE.Horseshoe
