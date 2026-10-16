-- Prove2me | Theorems.Thm_QAOAE3Lin2_Typical_typical_concentration
-- name    : QAOAE3Lin2.Typical.typical_concentration
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T10:59:03.549435+00:00
-- url     : https://prove2.me/theorems/6f1edbad-6cba-4811-9576-f885b6bff684
-- title:
--   Section III, p. 11, closing sentence (pinned Chebyshev form with (50)'s bound) — the fraction of instances below m/2 + (m/2) sin γ cos^{3D} γ − t is ⩽ m(6D+3)(D+1)/(4t²)
-- statement:
--   Fix any collection of $m$ triples forming an E3LIN2 family (three distinct bits per triple, no triple repeated) in which every bit lies in at most $D+1$ triples. Fix $\gamma$ with $0\le\gamma\le\pi/2$ and $t>0$. Choose the right-hand sides of the $m$ equations uniformly at random among the $2^m$ possibilities, run the level-one QAOA with angles $(-\gamma,\pi/4)$, and let $N$ be the expected number of satisfied equations of the measured string. Then
--   $$\Pr_d\Big[N\le\frac m2+\frac m2\sin\gamma\cos^{3D}\gamma-t\Big]\;\le\;\frac{m(6D+3)(D+1)}{4t^2}.$$
--
--   With $D$ fixed and $t=c\sqrt m$, the right side is the constant $(6D+3)(D+1)/(4c^2)$: for large $m$, on a typical instance, the QAOA satisfies in expectation at least $\big(\tfrac12+\tfrac12\sin\gamma\cos^{3D}\gamma\big)m$ minus a term of order $\sqrt m$ equations. At $\gamma=1/\sqrt{3D}$ this threshold is $\big(\tfrac12+\tfrac{1+o(1)}{2\sqrt{3e}D^{1/2}}\big)m$.
--
--   **Formalization Note** The paper's sentence ("with high probability … at least (54) minus a term of order $\sqrt m$") has no explicit failure probability. It is pinned here by combining the paper's own mean bound (50) and its variance bound $\tfrac14m(6D+3)(D+1)$ through Chebyshev's inequality, which the page invokes implicitly. The threshold uses (50)'s exact lower bound $\tfrac m2\sin\gamma\cos^{3D}\gamma$ rather than (54), because (54) is false as a finite-$D$ inequality ($\sin\gamma\cos^{3D}\gamma<1/\sqrt{3eD}$ for every $D\ge1$). The range $0\le\gamma\le\pi/2$ is added because (50)'s lower bound needs $\sin\gamma,\cos\gamma\ge0$; the paper's choice $\gamma=1/\sqrt{3D}$ lies in it. The probability is over the right-hand sides only; $N$ is the quantum expectation, not a single measurement outcome.
-- source:
--   Farhi, Goldstone, Gutmann, A Quantum Approximate Optimization Algorithm Applied to a Bounded Occurrence Constraint Problem, arXiv:1412.6062v2, p. 11, Section III, closing paragraph (with (50), p. 10, and the variance bound, p. 11)

import Mathlib
import Definitions.Def_QAOAE3Lin2_Typical_Setting

namespace QAOAE3Lin2.Typical

/-- §III, p. 11, closing sentence, pinned by Chebyshev's inequality from (50) and the variance
bound: for fixed triples with every bit in at most `D + 1` equations and `γ ∈ [0, π/2]`, the
fraction of the `2^m` right-hand-side choices on which the expected satisfied count of
`|−γ, π/4⟩` is at most `m/2 + (m/2) sin γ cos^{3D} γ − t` is at most `m(6D + 3)(D + 1)/(4t²)`. -/
theorem typical_concentration {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n) (D : ℕ)
    (htri : QAOAE3Lin2.General.IsTripleFamily tri) (hocc : QAOAE3Lin2.General.BoundedOccurrence tri D) (γ : ℝ) (hγ₀ : 0 ≤ γ)
    (hγ₁ : γ ≤ Real.pi / 2) (t : ℝ) (ht : 0 < t) :
    ((Finset.univ.filter fun rhs : Fin m → Bool =>
        QAOAE3Lin2.General.expSat tri rhs (-γ) (Real.pi / 4) ≤
          (m : ℝ) / 2 + (m : ℝ) / 2 * Real.sin γ * Real.cos γ ^ (3 * D) - t).card : ℝ) / 2 ^ m ≤
      (m : ℝ) * (6 * D + 3) * (D + 1) / (4 * t ^ 2) := by sorry

end QAOAE3Lin2.Typical
