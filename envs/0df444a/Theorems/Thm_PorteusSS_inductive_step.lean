-- Prove2me | Theorems.Thm_PorteusSS_inductive_step
-- name    : PorteusSS.inductive_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T17:58:37.964368+00:00
-- url     : https://prove2.me/theorems/982cd66c-f4bd-4c32-803d-9ebc9091428f
-- title:
--   Lemma 3 — the inductive step: $G_{cn} \in C(K_c)$, nonincreasing on $R^-$, and $Y_n(x) \neq \emptyset$
-- statement:
--   Consider the inventory model of §§II–III under its standing assumptions, with $m$ piecewise continuous. Suppose that, for a given $n \ge 1$,
--
--   1. $f_{n-1}$ is piecewise continuous and PF-integrable,
--   2. $c_\infty\cdot + f_{n-1}$ is nonincreasing on $R^- = (-\infty, 0)$,
--   3. $\kappa\cdot + f_{n-1}$ is non-$K_\kappa$-decreasing on $\mathbb R$ for every $\kappa \in C$,
--
--   and that A1–A4 hold. Then for every $\kappa \in C$,
--   $$ G_{\kappa n} \in C(K_\kappa) \quad\text{and}\quad G_{\kappa n} \text{ is nonincreasing on } R^-, $$
--   and $Y_n(x)$ is nonempty for every $x \in \mathbb R$.
--
--   Together with Theorem 2 this gives the optimal policy in period $n$; the main theorem then verifies (i)–(iii) for every period by induction.
--
--   **Formalization Note.** The paper uses without stating it that $m$ is piecewise continuous (proof of Lemma 3: "since $m$ and $f_{n-1}$ are piecewise continuous"); it is the hypothesis `hm_pc`. Here $f_{n-1}$ is the value function of the recursion (4) built from the data, with $f_0$ the terminal cost.
-- source:
--   Porteus, On the Optimality of Generalized (s, S) Policies, Management Science 17(7):411–426 (1971), p. 418, Lemma 3

import Mathlib
import Definitions.Def_PorteusSS_Functions
import Definitions.Def_PorteusSS_OrderingCost
import Definitions.Def_PorteusSS_Model

open MeasureTheory Filter Topology Set

namespace PorteusSS

/-- Lemma 3 (p. 418). In the model of §§II–III, with `m` piecewise continuous, if for a given
`n ≥ 1` (i) `f_{n-1}` is piecewise continuous and PF-integrable, (ii) `c_∞· + f_{n-1}` is
nonincreasing on `R⁻`, (iii) `κ· + f_{n-1}` is non-`K_κ`-decreasing on `ℝ` for `κ ∈ C`, and
A1–A4 hold, then for every `κ ∈ C`, `G_{κ n} ∈ C(K_κ)` and `G_{κ n}` is nonincreasing on `R⁻`,
and `Y_n(x)` is nonempty for every `x ∈ ℝ`. -/
theorem inductive_step (c m φ f0 : ℝ → ℝ) (α c0 K0 cInf KInf : ℝ)
    (hmodel : IsModel c m φ α c0 K0 cInf KInf) (hm_pc : PiecewiseContinuousOn m univ)
    (n : ℕ) (hn : 1 ≤ n)
    (hi : PiecewiseContinuousOn (valueFn c m φ f0 α (n - 1)) univ ∧
      PFIntegrable (valueFn c m φ f0 α (n - 1)))
    (hii : AntitoneOn (fun x => cInf * x + valueFn c m φ f0 α (n - 1) x) (Iio 0))
    (hiii : ∀ κ ∈ slopeSet c,
      NonKDecreasingOn (fun x => κ * x + valueFn c m φ f0 α (n - 1) x) (Kc c κ) univ)
    (hA1 : AssumptionA1 m α c0 cInf) (hA2 : AssumptionA2 m α c0 cInf)
    (hA3 : AssumptionA3 c m α) (hA4 : AssumptionA4 m α cInf) :
    (∀ κ ∈ slopeSet c,
      CK (Kc c κ) (Gfn c m φ f0 α κ n) ∧ AntitoneOn (Gfn c m φ f0 α κ n) (Iio 0)) ∧
    ∀ x : ℝ, (Yset c m φ f0 α n x).Nonempty := by sorry

end PorteusSS
