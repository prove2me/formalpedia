-- Prove2me | Theorems.Thm_TIESharp_lemma_4_1
-- name    : TIESharp.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:39:17.625072+00:00
-- url     : https://prove2.me/theorems/8de9f43c-59fb-41e7-a23f-b7d8b8b63fa5
-- title:
--   Lemma 4.1 — normalized potentials are concave, monotone, 1-Lipschitz, with $0\le V^m_i\le\sum_j t_{ij}$
-- statement:
--   Let $F$ be a feasible truthful-in-expectation family. Replacing every payment by the normalized payment $\bar p^m_i(t)=p^m_i(t)-p^m_i(0,t_{-i})$ does not change the allocations and keeps the family feasible and truthful in expectation. Moreover, for every job count $m$, nonnegative profile $t$ and machine $i$:
--   1. $\bar p^m_i(0,t_{-i})=0$ and $-\|t_i\|_1\le\bar p^m_i(t)\le0$;
--   2. for fixed $t_{-i}$, the potential $V^m_i(t)=t_i\cdot q^m_i(t)-\bar p^m_i(t)$ is, as a function of the own row on $[0,\infty)^m$, concave, coordinatewise nondecreasing and $1$-Lipschitz in the $\ell^1$ norm;
--   3. for all types $u,v\in[0,\infty)^m$,
--   $$V^m_i(v,t_{-i})\le V^m_i(u,t_{-i})+(v-u)\cdot q^m_i(u,t_{-i});\tag{4.1}$$
--   4. $0\le V^m_i(t)\le\sum_j t_{ij}$.
--
--   This is the concave (Rochet) form of truthfulness in expectation: the potential is an infimum of affine functions of the own row, and the assignment probabilities are its supergradients.
--
--   Differences from the source:
--   - generalization: §4's standing assumption n ≥ 2 (p.13) → every n; reason: the proof uses only (2.1) at fixed opponents' bids; the n ≥ 2 case is a specialization
--   - encoding: the family can be normalized without changing its allocations → the family ⟨alloc, p̄⟩ is feasible and truthful in expectation, and the clauses are stated for p̄ and V computed from the given payments; reason: same objects; the normalization is explicit
--   - encoding: a family: one assignment distribution and one finite expected-payment vector per job count, on bids in [0,∞)^{n×m} → Family n with real weights alloc and real payments pay, plus IsFeasible (weights nonnegative and summing to one at every nonnegative bid profile); values at profiles with a negative entry are unconstrained; reason: Lean convention for a distribution on the finite set of assignments; same families
-- source:
--   Li, Sharp Bounds for Truthful-in-Expectation Scheduling, arXiv:2611.05134 (held version, sha256 e611c390…b70e5481), Lemma 4.1, p.13

import Mathlib
import Definitions.Def_TIESharp_IsFeasible
import Definitions.Def_TIESharp_IsTIE
import Definitions.Def_TIESharp_potential

set_option autoImplicit false

namespace TIESharp

/-- **Lemma 4.1 (Normalized potentials)** (Li, *Sharp Bounds for Truthful-in-Expectation
Scheduling*, arXiv:2611.05134, Lemma 4.1, p.13). Let `F` be a feasible truthful-in-expectation
family. Replacing every payment by the normalized payment `p̄^m_i(t) = p^m_i(t) − p^m_i(0, t_{-i})`
leaves the allocations unchanged and keeps the family feasible and truthful in expectation; and at
every nonnegative profile `t`, every machine `i`:
`p̄^m_i(0, t_{-i}) = 0` and `−‖t_i‖₁ ≤ p̄^m_i(t) ≤ 0`; for fixed `t_{-i}` the potential
`V^m_i = t_i · q^m_i − p̄^m_i`, as a function of the own row on `[0, ∞)^m`, is concave,
coordinatewise nondecreasing and `1`-Lipschitz in the `ℓ¹` norm; for all `u, v ∈ [0, ∞)^m`,
`V^m_i(v, t_{-i}) ≤ V^m_i(u, t_{-i}) + (v − u) · q^m_i(u, t_{-i})` (4.1); and
`0 ≤ V^m_i(t) ≤ Σ_j t_ij`.

**Formalization Note.** The normalized family is `⟨F.alloc, pbar F⟩`. `(u, t_{-i})` is
`Function.update t i u`; `u ≤ v` is the coordinatewise order on `Fin m → ℝ`. -/
theorem lemma_4_1 (n : ℕ) (F : Family n) (hF : IsFeasible F) (hT : IsTIE F) :
    (IsFeasible (⟨F.alloc, fun m b i => pbar F m b i⟩ : Family n) ∧
      IsTIE (⟨F.alloc, fun m b i => pbar F m b i⟩ : Family n)) ∧
    ∀ (m : ℕ) (t : Fin n → Fin m → ℝ) (i : Fin n), Nonneg t →
      pbar F m (Function.update t i 0) i = 0 ∧
      -∑ j, t i j ≤ pbar F m t i ∧ pbar F m t i ≤ 0 ∧
      ConcaveOn ℝ {x : Fin m → ℝ | ∀ j, 0 ≤ x j}
        (fun x => potential F m (Function.update t i x) i) ∧
      (∀ u v : Fin m → ℝ, (∀ j, 0 ≤ u j) → u ≤ v →
        potential F m (Function.update t i u) i ≤ potential F m (Function.update t i v) i) ∧
      (∀ u v : Fin m → ℝ, (∀ j, 0 ≤ u j) → (∀ j, 0 ≤ v j) →
        |potential F m (Function.update t i v) i - potential F m (Function.update t i u) i|
          ≤ ∑ j, |v j - u j|) ∧
      (∀ u v : Fin m → ℝ, (∀ j, 0 ≤ u j) → (∀ j, 0 ≤ v j) →
        potential F m (Function.update t i v) i ≤
          potential F m (Function.update t i u) i
            + ∑ j, (v j - u j) * marg F m (Function.update t i u) i j) ∧
      0 ≤ potential F m t i ∧ potential F m t i ≤ ∑ j, t i j := by sorry

end TIESharp
