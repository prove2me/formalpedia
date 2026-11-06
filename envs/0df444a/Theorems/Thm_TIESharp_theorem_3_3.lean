-- Prove2me | Theorems.Thm_TIESharp_theorem_3_3
-- name    : TIESharp.theorem_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:42:24.674558+00:00
-- url     : https://prove2.me/theorems/9f142dda-dfd2-4974-bd5a-733103d2995d
-- title:
--   Theorem 3.3 — Bounded-Square allocation with slot rounding: TIE, ratio $(n+1)/2$ for $n\ge7$
-- statement:
--   Let $n\ge2$. The Bounded-Square allocation rule with slot rounding gives a truthful-in-expectation mechanism for every finite number of jobs. For $n\ge7$ its expected makespan is at most $(n+1)\,\mathrm{OPT}(t)/2$. For $n=4,5,6$, the respective upper bounds are $3\,\mathrm{OPT}(t)$, $(105/32)\,\mathrm{OPT}(t)$ and $(29/8)\,\mathrm{OPT}(t)$. Expected payments are finite. If $\mathrm{OPT}(t)=0$, every supported assignment has zero makespan.
--
--   In detail: (i) at every job count and nonnegative profile a slot-rounding law of the Bounded-Square probabilities exists; (ii) every family whose laws are such slot-rounding laws and whose payments are $p_i=\sum_j\pi_{ij}$ with $\pi_{ij}(t)=t_{ij}q_{ij}(t)+\int_{t_{ij}}^\infty q_{ij}(u,t_{-ij})\,du$ is truthful in expectation; (iii) the payment integrands are integrable; (iv) every such law satisfies the makespan bounds; (v) the zero-optimum clause.
--
--   Differences from the source:
--   - generalization: the slot rounding of Sec. 3.2/5.2 (one fixed decomposition) → every slot-rounding law (IsBSSlotLaw): existence, truthfulness and the bounds for all of them; reason: the paper's decomposition is one such law, and the bounds "hold for every such decomposition" (p.23)
--   - encoding: gives a truthful-in-expectation mechanism; expected payments are finite → a law exists at every profile, every family with these laws and payments is IsTIE, and the payment integrands are IntegrableOn (t_ij, ∞); reason: the mechanism is any choice of such laws with these payments
-- source:
--   Li, Sharp Bounds for Truthful-in-Expectation Scheduling, arXiv:2611.05134 (held version, sha256 e611c390…b70e5481), Theorem 3.3, p.10 (n ≥ 2 from §2, p.4)

import Mathlib
import Definitions.Def_TIESharp_IsTIE
import Definitions.Def_TIESharp_opt
import Definitions.Def_TIESharp_IsBSSlotLaw
import Definitions.Def_TIESharp_bsPay

set_option autoImplicit false

namespace TIESharp

/-- **Theorem 3.3 (Bounded-Square allocation with slot rounding)** (Li, *Sharp Bounds for
Truthful-in-Expectation Scheduling*, arXiv:2611.05134, Theorem 3.3, p.10). Let `n ≥ 2`. The
Bounded-Square allocation rule with slot rounding gives a truthful-in-expectation mechanism for
every finite number of jobs. For `n ≥ 7` its expected makespan is at most `(n+1) OPT(t)/2`. For
`n = 4, 5, 6`, the respective upper bounds are `3 OPT(t)`, `(105/32) OPT(t)` and `(29/8) OPT(t)`.
Expected payments are finite. If `OPT(t) = 0`, every supported assignment has zero makespan.

Clauses: (i) at every job count and nonnegative profile a slot-rounding law of the Bounded-Square
probabilities exists; (ii) every family whose laws are such slot-rounding laws and whose payments
are `p_i = Σ_j π_ij` with `π_ij = t_ij q_ij + ∫_{t_ij}^∞ q_ij(u, t_{-ij}) du` is truthful in
expectation; (iii) the payment integrands are integrable, so the payments are finite;
(iv) the makespan bounds; (v) the zero-optimum clause.

**Formalization Note.** `n ≥ 2` is the standing assumption of §§3–5 (p.4). The slot rounding is any
law with the Bounded-Square marginals supported on slot-feasible assignments (`IsBSSlotLaw`): it
contains every decomposition of Sec. 5.2, and the bounds are claimed for all of them.
`E[C_max] = Σ_A y_A C_max(t, A)`. -/
theorem theorem_3_3 (n : ℕ) (hn : 2 ≤ n) :
    (∀ (m : ℕ) (t : Fin n → Fin m → ℝ), Nonneg t → ∃ y, IsBSSlotLaw t y) ∧
    (∀ F : Family n,
      (∀ (m : ℕ) (b : Fin n → Fin m → ℝ), Nonneg b →
        IsBSSlotLaw b (F.alloc m b) ∧ ∀ i, F.pay m b i = ∑ j, bsPay b i j) →
      IsTIE F) ∧
    (∀ (m : ℕ) (t : Fin n → Fin m → ℝ) (i : Fin n) (j : Fin m), Nonneg t →
      MeasureTheory.IntegrableOn (fun u => bsCol (Function.update (fun k => t k j) i u) i)
        (Set.Ioi (t i j))) ∧
    (∀ (m : ℕ) (t : Fin n → Fin m → ℝ) (y : (Fin m → Fin n) → ℝ), Nonneg t → IsBSSlotLaw t y →
      (7 ≤ n → ∑ A, y A * MatousekLP.Scheduling.makespan (Matrix.of t) A
          ≤ ((n : ℝ) + 1) / 2 * opt t) ∧
      (n = 4 → ∑ A, y A * MatousekLP.Scheduling.makespan (Matrix.of t) A ≤ 3 * opt t) ∧
      (n = 5 → ∑ A, y A * MatousekLP.Scheduling.makespan (Matrix.of t) A ≤ 105 / 32 * opt t) ∧
      (n = 6 → ∑ A, y A * MatousekLP.Scheduling.makespan (Matrix.of t) A ≤ 29 / 8 * opt t) ∧
      (opt t = 0 → ∀ A, 0 < y A → MatousekLP.Scheduling.makespan (Matrix.of t) A = 0)) := by sorry

end TIESharp
