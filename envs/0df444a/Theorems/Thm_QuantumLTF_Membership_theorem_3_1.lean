-- Prove2me | Theorems.Thm_QuantumLTF_Membership_theorem_3_1
-- name    : QuantumLTF.Membership.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:38:55.46558+00:00
-- url     : https://prove2.me/theorems/7d3b2e69-823e-47a3-bb1c-10ee884058dc
-- title:
--   Theorem 3.1 — estimating the boundary offset by binary search
-- statement:
--   Let $n\ge2$, $0<\epsilon\le1/2$, $0<\zeta<1$, $p\in\mathbb R^n$. There is a deterministic algorithm with $O(\log(L_\epsilon/\zeta))$ membership queries, depending on $p,\epsilon,\zeta$ only, such that for every unit $w$ and every $\theta$ with $1/10\le|\langle w,p\rangle|\le3$ and $|h_p(0)|\le L_\epsilon$ it returns $s=\mathrm{sign}(\langle w,p\rangle)$ and a value $\tilde h_p(0)$ with
--   $$|\tilde h_p(0)-h_p(0)|\le\zeta,$$
--   and $\tilde h_p(0)$ is exactly a signed fixed-point number of $O(\log(L_\epsilon/\zeta))$ bits. It locates the separating hyperplane along the reference line $\mathbb Rp$.
--
--   Differences from the source:
--   - encoding: a deterministic algorithm using membership queries → a QueryTree with real query points, depth bounded; reason: a deterministic adaptive query algorithm is a decision tree; the statement does not restrict its query points
--   - reading: O(·) in a statement → one universal constant C placed before n and the other parameters; reason: the O(·) of the paper is uniform in all the stated parameters
--   - reading: a deterministic algorithm with membership-query access to f_{w,θ} → one tree T, with its format (B, f), chosen before w and θ and depending only on n, ϵ, ζ, p; reason: the algorithm sees w and θ only through its queries; the proof on pp. 21–22 builds it from L_ϵ, ζ and p
--   - encoding: h̃_p(0) represented exactly in signed fixed-point form using O(log(L_ϵ/ζ)) bits → IsFp B f: h̃ = k/2^f with |k| < 2^B and f ≤ B; reason: B counts integer and fractional bits together, Eq. (37)
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Theorem 3.1, Eq. (27), p. 21 (PDF p. 22)

import Mathlib
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_height
import Definitions.Def_QuantumLTF_Membership_Leps
import Definitions.Def_QuantumLTF_Membership_IsFp
import Definitions.Def_QuantumLTF_Membership_QueryTree

namespace QuantumLTF.Membership

/-- **Theorem 3.1 (Estimating the boundary offset).** Krivcenko, Nguyen, de Wolf, *Fast Quantum Algorithms for Learning Linear Threshold Functions*,
arXiv:2609.40331, Theorem 3.1, p. 21 (PDF p. 22), Eq. (27).
For `n ≥ 2`, `0 < ϵ ≤ 1/2`, `0 < ζ < 1`, on the event `1/10 ≤ |⟨w, p⟩| ≤ 3`, if `|h_p(0)| ≤ L_ϵ` then a
deterministic algorithm with `O(log(L_ϵ/ζ))` membership queries returns `s = sign(⟨w, p⟩)` and `h̃_p(0)`
with `|h̃_p(0) − h_p(0)| ≤ ζ`, where `h̃_p(0)` is an exact signed fixed-point number of `O(log(L_ϵ/ζ))` bits.

**Formalization Note.** The algorithm is a `QueryTree`, which may depend on `p, ϵ, ζ` but not on
`w, θ`; so may the format `(B, f)`. `∃ C` precedes `n`. -/
theorem theorem_3_1 :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∀ ε ζ : ℝ, 0 < ε → ε ≤ 1 / 2 → 0 < ζ → ζ < 1 →
      ∀ p : EuclideanSpace ℝ (Fin n),
        ∃ (B f : ℕ) (T : QueryTree n (ℤ × ℝ)),
          (T.depth : ℝ) ≤ C * Real.log (Leps ε / ζ) ∧ (B : ℝ) ≤ C * Real.log (Leps ε / ζ) ∧
          ∀ (w : EuclideanSpace ℝ (Fin n)) (θ : ℝ), ‖w‖ = 1 →
            1 / 10 ≤ |inner ℝ w p| → |inner ℝ w p| ≤ 3 → |height w θ p 0| ≤ Leps ε →
              (T.run (ltf w θ)).1 = sgn (inner ℝ w p) ∧
              |(T.run (ltf w θ)).2 - height w θ p 0| ≤ ζ ∧
              IsFp B f (T.run (ltf w θ)).2 := by sorry

end QuantumLTF.Membership
