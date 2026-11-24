-- Prove2me | Theorems.Thm_SteinitzExchange_Duality_Supplement_flow_potential_criterion
-- name    : SteinitzExchange.Duality.Supplement.flow_potential_criterion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T04:35:21.714908+00:00
-- url     : https://prove2.me/theorems/3370c5d5-acac-41b6-aae3-5d111a206fd5
-- title:
--   Theorem 7.6 (corrected: integral arc weights in the integer addendum)
-- statement:
--   Let the network have disjoint entrance and exit sets, integer lower and upper capacities and real arc weights $w$. Let the finite nonempty domains $B^+,B^-$ carry functions $\omega^+,\omega^-$ satisfying (EXC), and let $\varphi$ be feasible for Problem P. Then
--   $$\varphi\text{ is optimal}\quad\Longleftrightarrow\quad\exists q:V\to\mathbb R,\ (i)\text{–}(iii)\text{ of Theorem 7.6 hold}.$$
--   If both boundary valuations and the arc weights are integer-valued, an optimal flow has such a potential in $\mathbb Z^V$. Finally, any potential certifying one optimum characterizes all other feasible optima by the same conditions (i)–(iii).
--
--   **Formalization Note.** The real equivalence and the fixed-potential clause retain every source assumption and conclusion. The printed integer addendum omits integrality of $w$ and is false: a single arc of weight $1/2$, capacities $0,2$, and boundary domains forcing flow $1$ requires $q(s)-q(t)=1/2$. The repaired integer clause adds integrality of $w$ only in that clause. With integral data, local boundary optimality and arc conditions are difference inequalities with integral bounds, so rounding down a real certifying potential preserves them. `DISPROOF.md` retains the instance and the repair's scope.
--
--   Differences from the source:
--   - correction: integer-valued boundary functions suffice for an integer potential, with arbitrary real arc weights → the integer addendum also assumes integral arc weights; the real and fixed-potential clauses are unchanged; reason: a one-arc interior flow of weight 1/2 forces a noninteger potential difference; integral difference bounds justify the repaired clause
-- source:
--   Murota, Convexity and Steinitz's Exchange Property, Adv. Math. 124 (1996), p. 307, Theorem 7.6

import Mathlib
import Definitions.Def_SteinitzExchange_Duality_Exchange
import Definitions.Def_SteinitzExchange_Duality_Supplement_NetworkOptimality

namespace SteinitzExchange.Duality.Supplement

/-- Theorem 7.6, pp. 307–308. Corrected integer addendum: arc weights as well
as the two boundary valuations must be integral. With w=1/2 on one interior
arc, an integer potential cannot exist; see DISPROOF.md. All real-valued
claims and the fixed-potential characterization are retained. -/
theorem flow_potential_criterion {N A : Type*} [Fintype N] [DecidableEq N] [Fintype A]
    (tail head : A → N) (Vp Vm : Finset N) (hdisj : Disjoint Vp Vm)
    (lo up : A → ℤ) (w : A → ℝ)
    (Bp : Finset (Vp → ℤ)) (Bm : Finset (Vm → ℤ))
    (hBp : Bp.Nonempty) (hBm : Bm.Nonempty)
    (ωp : (Vp → ℤ) → ℝ) (ωm : (Vm → ℤ) → ℝ)
    (hωp : SatisfiesEXC Bp ωp) (hωm : SatisfiesEXC Bm ωm)
    (φ : A → ℤ) (hφ : IsProblemFlow tail head Vp Vm lo up Bp Bm φ) :
    (IsOptimalFlow tail head Vp Vm lo up w Bp Bm ωp ωm φ ↔
      ∃ q : N → ℝ, PotentialCertificate tail head Vp Vm lo up w Bp Bm ωp ωm φ q) ∧
    ((∀ x ∈ Bp, ∃ k : ℤ, ωp x = k) → (∀ x ∈ Bm, ∃ k : ℤ, ωm x = k) →
      (∀ a, ∃ k : ℤ, w a = k) →
      IsOptimalFlow tail head Vp Vm lo up w Bp Bm ωp ωm φ →
      ∃ q : N → ℤ,
        PotentialCertificate tail head Vp Vm lo up w Bp Bm ωp ωm φ (fun v => (q v : ℝ))) ∧
    (∀ (q : N → ℝ), PotentialCertificate tail head Vp Vm lo up w Bp Bm ωp ωm φ q →
      ∀ ψ : A → ℤ, IsProblemFlow tail head Vp Vm lo up Bp Bm ψ →
        (IsOptimalFlow tail head Vp Vm lo up w Bp Bm ωp ωm ψ ↔
          PotentialCertificate tail head Vp Vm lo up w Bp Bm ωp ωm ψ q)) := by sorry

end SteinitzExchange.Duality.Supplement
