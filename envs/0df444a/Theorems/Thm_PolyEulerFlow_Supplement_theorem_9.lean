-- Prove2me | Theorems.Thm_PolyEulerFlow_Supplement_theorem_9
-- name    : PolyEulerFlow.Supplement.theorem_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:08:03.279559+00:00
-- url     : https://prove2.me/theorems/48dfa7d3-3e33-45aa-9e25-f9b89358dff8
-- title:
--   Theorem 9 — PSPACE is eventual robust decision, with or without the horizon $2^{cs}$
-- statement:
--   Let $d\in\mathbb N$ and $L\subseteq\mathbb N^d$. The following are equivalent.
--
--   1. $L\in\mathsf{PSPACE}$.
--   2. A scale-controlled rational polynomial system **eventually decides $L$ robustly at unit step**, with a polynomial threshold $S$ and a precision exponent $r>0$: for every $x$, every $s\ge S(\ell(x))$, $h=2^{-s}$, and every orbit $z_0=c(x,h)$, $z_{k+1}=z_k+F(x,h,z_k)+\xi_k$ with $\|\xi_k\|_\infty\le h^r$, the whole orbit stays in one fixed compact box and $|z_k(o)-1_L(x)|\le1/4$ for all $k\ge k_0$, for some index $k_0$ that may depend on the orbit.
--   3. Such a system eventually decides $L$ robustly **mesh-uniformly**: the same field, initialization, threshold, output coordinate, box and precision exponent work at every step $0<\eta\le1$ (orbits $z_{k+1}=z_k+\eta F(x,h,z_k)+\eta\xi_k$).
--
--   The equivalence is unchanged when items 2 and 3 also require a common physical stabilization horizon $2^{cs}$ for a fixed $c>0$, that is, $|z_k(o)-1_L(x)|\le1/4$ for every $k\ge\lceil2^{cs}/\eta\rceil$.
--
--   Moreover, for $L\in\mathsf{PSPACE}$ there is a witness of the horizon form of item 3 which also, for every $x$ and $s\ge S(\ell(x))$:
--
--   1. on every admissible variable mesh ($0<\eta_k\le1$, $\sum\eta_k=\infty$) with disturbances $\|\xi_k\|_\infty\le h^r$, stays in the box and is correct at every index of physical time $\sum_{i<k}\eta_i\ge2^{cs}$;
--   2. for every measurable forcing with $\|\xi(t)\|_\infty\le h^r$ a.e., has a solution of $\dot z=F(x,h,z)+\xi(t)$, $z(0)=c(x,h)$, on $[0,\infty)$, and every such solution stays in the box and satisfies $|z(t)(o)-1_L(x)|\le1/4$ for all $t\ge2^{cs}$.
--
--   Polynomial space is exactly what a compact rational polynomial dynamics decides robustly, with no stabilization time supplied.
--
--   **Formalization Note** The conclusion has five conjuncts: $1\Leftrightarrow2$, $1\Leftrightarrow3$, $1\Leftrightarrow2'$, $1\Leftrightarrow3'$ (primed: with the horizon), and the witness clause. The exponents $r$ and $c$ are real.
--
--   Differences from the source:
--   - encoding: integer polynomial scale threshold → a polynomial with natural coefficients; reason: every integer polynomial is dominated by one with natural coefficients and correctness is required at every larger scale
--   - encoding: L ∈ PSPACE for L ⊆ ℕ^d → the published InPSPACE on the self-delimiting encoding encodeNatVec; reason: standard binary input of linear length for fixed d
--   - encoding: one fixed compact box → a coordinatewise box [lo, hi] with real corners; reason: every compact set lies in such a box
--   - reading: item 3: the same field, initialization, compact box and precision exponent for every 0 < η ≤ 1 → also the same threshold S and output coordinate o for every η; reason: Definition 6 fixes S and o with the system; the stronger right-hand side makes 1 ⇒ 3 stronger, and 3 ⇒ 2 is unaffected
--   - reading: the constructed witnesses meet this stronger requirement, including for variable meshes and continuous forcing → for L ∈ PSPACE there is a horizon witness of item 3 that also stays in the box and is correct at physical time ≥ 2^{cs} on every admissible variable mesh with drift ≤ h^r, and for every measurable forcing ≤ h^r has a forced solution, every one staying in the box and correct for t ≥ 2^{cs}; reason: the witnesses are not named objects; existence of the forced solution is part of the continuous decision (Corollary 50, p.38: the solution exists globally)
-- source:
--   Bournez, One Polynomial Field for Every Euler Step and the Flow: Polynomial Dynamics for P and PSPACE (manuscript, STOC 2027 submission, sha256 c4e01b2beb237b48b48e97294deb3c15dae11d39c5f136914567c5ca2ae1b119), Theorem 9, p.7 (PDF 9); Definitions 3, 5, 6, pp.5–6; proof p.35 (PDF 37); Corollary 50, p.38

import Mathlib
import Definitions.Def_PolyEulerFlow_Supplement_ScaleSystem
import Definitions.Def_PolyEulerFlow_IsForcedSolution

namespace PolyEulerFlow.Supplement

open PolyEulerFlow

/-- **Theorem 9 (Polynomial space without a supplied horizon)**, p.7 (PDF 9). Bournez, One Polynomial Field for Every Euler Step and the
Flow (manuscript, sha256 c4e01b2b…): "For every language L ⊆ ℕ^d, the following are equivalent. 1. L ∈ PSPACE. 2. A unit-step
scale-controlled rational polynomial system eventually decides L robustly, with polynomial scale threshold and precision exponent r > 0.
3. Such a system eventually decides L robustly and mesh-uniformly, with the same field, initialization, compact box and precision exponent for
every 0 < η ≤ 1. The equivalence is unchanged if Items 2 and 3 additionally require a common physical stabilization horizon 2^{cs}, for a
fixed c > 0. The constructed witnesses meet this stronger requirement, including for variable meshes and continuous forcing."

The conclusion has five parts: `1 ⇔ 2`, `1 ⇔ 3`, `1 ⇔ 2′`, `1 ⇔ 3′` (the primed items with the horizon `2^{cs}`), and, for `L ∈ PSPACE`, a
witness of `3′` that also, for every admissible variable mesh and every disturbance `‖ξ_k‖∞ ≤ h^r`, stays in the box and is correct at
every grid index of physical time `≥ 2^{cs}`, and, for every measurable forcing `‖ξ(t)‖∞ ≤ h^r`, has a forced solution, every forced solution
staying in the box and being correct at every time `t ≥ 2^{cs}`.

**Formalization Note.** Thresholds are polynomials with natural coefficients; `r` and `c` are real; the threshold and the output coordinate
are fixed together with the field, initialization, box and precision exponent, before `η`. -/
theorem theorem_9 {d : ℕ} (L : Set (Fin d → ℕ)) :
    (InPSPACE L ↔ ∃ (m : ℕ) (S : ScaleSystem d m) (Sthr : Polynomial ℕ) (o : Fin m) (lo hi : Fin m → ℝ) (r : ℝ),
        0 < r ∧ S.EventuallyRobustAt L Sthr r o lo hi 1) ∧
    (InPSPACE L ↔ ∃ (m : ℕ) (S : ScaleSystem d m) (Sthr : Polynomial ℕ) (o : Fin m) (lo hi : Fin m → ℝ) (r : ℝ),
        0 < r ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → S.EventuallyRobustAt L Sthr r o lo hi η) ∧
    (InPSPACE L ↔ ∃ (m : ℕ) (S : ScaleSystem d m) (Sthr : Polynomial ℕ) (o : Fin m) (lo hi : Fin m → ℝ) (r c : ℝ),
        0 < r ∧ 0 < c ∧ S.RobustHorizonAt L Sthr r c o lo hi 1) ∧
    (InPSPACE L ↔ ∃ (m : ℕ) (S : ScaleSystem d m) (Sthr : Polynomial ℕ) (o : Fin m) (lo hi : Fin m → ℝ) (r c : ℝ),
        0 < r ∧ 0 < c ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → S.RobustHorizonAt L Sthr r c o lo hi η) ∧
    (InPSPACE L → ∃ (m : ℕ) (S : ScaleSystem d m) (Sthr : Polynomial ℕ) (o : Fin m) (lo hi : Fin m → ℝ) (r c : ℝ),
        0 < r ∧ 0 < c ∧ (∀ η : ℝ, 0 < η → η ≤ 1 → S.RobustHorizonAt L Sthr r c o lo hi η) ∧
        ∀ (x : Fin d → ℕ) (s : ℕ), Sthr.eval (vecLength x) ≤ s →
          (∀ (η : ℕ → ℝ) (ξ : ℕ → Fin m → ℝ), IsAdmissibleMesh η → IsPermittedDisturbance (scale s ^ r) ξ →
            (∀ k, eulerOrbit (S.field x (scale s)) (S.init x (scale s)) η ξ k ∈ Set.Icc lo hi) ∧
            ∀ k : ℕ, (2 : ℝ) ^ (c * s) ≤ physTime η k →
              |eulerOrbit (S.field x (scale s)) (S.init x (scale s)) η ξ k o - langIndicator L x| ≤ 1 / 4) ∧
          ∀ ξ : ℝ → Fin m → ℝ, IsPermittedForcing (scale s ^ r) ξ →
            (∃ z : ℝ → Fin m → ℝ, IsForcedSolution (S.field x (scale s)) (S.init x (scale s)) ξ z) ∧
            ∀ z : ℝ → Fin m → ℝ, IsForcedSolution (S.field x (scale s)) (S.init x (scale s)) ξ z →
              (∀ t : ℝ, 0 ≤ t → z t ∈ Set.Icc lo hi) ∧
              ∀ t : ℝ, (2 : ℝ) ^ (c * s) ≤ t → |z t o - langIndicator L x| ≤ 1 / 4) := by sorry

end PolyEulerFlow.Supplement
