-- Prove2me | Theorems.Thm_RSCapacity_lemma_6_7
-- name    : RSCapacity.lemma_6_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:28:48.292037+00:00
-- url     : https://prove2.me/theorems/dce34ba2-8a1c-4b29-9066-649121246e9f
-- title:
--   Lemma 6.7 (Polynomial degree of the lifted jet)
-- statement:
--   In the setting of Lemma 6.6, assume (56): $\deg_ZQ,\deg_XQ\le D$, $\deg^{\mathrm{tot}}_YQ\le B<p$ and $D\ge2$. On the open set $H_\alpha\neq0$ the equations $F_{\alpha,t}=0$, $1\le t\le d-s$, recursively determine
--   $$c_{s+t}=\frac{N_t(Z,c_0,\dots,c_s)}{H_\alpha(Z,c_0,\dots,c_s)^{2t-1}},\qquad\deg N_t\le(2t-1)(D+B).$$
--   If $Q$ is independent of $Z$, the same holds with $D+B$ replaced by $B$.
--
--   So the Taylor jet of a nonsingular solution is a rational function of bounded degree in the base variables $(Z,c_0,\dots,c_s)$.
--
--   Differences from the source:
--   - encoding: F of characteristic p with d < p → d < ringChar F; reason: characteristic 0 is excluded exactly as on the page
--   - reading: the equations recursively determine c_{s+t} = N_t/H_α^{2t−1} → ∃ polynomials N_t in Z, c_0, …, c_s of total degree ≤ (2t − 1)(D + B) such that at every point with H_α ≠ 0, F_{α,t} = 0 for all 1 ≤ t ≤ d − s iff c_{s+t} = N_t/H_α^{2t−1} for all 1 ≤ t ≤ d − s; reason: the meaning of determining the jet on H_α ≠ 0
-- source:
--   Jeronimo, Algorithmic List Decoding at Capacity and Optimal Proximity Gaps for Reed–Solomon Codes, arXiv:2609.05870 (held version of November 1, 2026, sha256 9a0069bd…), Lemma 6.7, p.26 (PDF 28); Equation (56), p.25 (PDF 27)

import Mathlib
import Definitions.Def_RSCapacity_JetCoefficients

set_option autoImplicit false

namespace RSCapacity

open MvPolynomial

/-- **Lemma 6.7 (Polynomial degree of the lifted jet).** Jeronimo, arXiv:2609.05870 (held version
of November 1, 2026, sha256 9a0069bd…), Lemma 6.7, p.26 (PDF 28), in the setting of Lemma 6.6
(§6.3, p.25; §6.3.1, p.26). Assume Equation (56) (deg_Z Q, deg_X Q ≤ D, deg^tot_Y Q ≤ B < p,
D ≥ 2). On the open set H_α ≠ 0, the equations F_{α,t} = 0, 1 ≤ t ≤ d − s, recursively determine
c_{s+t} = N_t(Z, c_0, …, c_s) / H_α(Z, c_0, …, c_s)^{2t−1} (62), where
deg N_t ≤ (2t − 1)(D + B) (63). If Q is independent of Z, the same bound holds with D + B replaced
by B.

**Formalization Note.**
* N_t is a polynomial in the base variables Z, c_0, …, c_s (variables of index at most s + 1 of
  F[Z, c_0, …, c_d]); deg is the total degree.
* "Recursively determine" is `IsLiftedJet`: at every point with H_α ≠ 0, the system
  F_{α,t} = 0 (1 ≤ t ≤ d − s) holds if and only if c_{s+t} = N_t / H_α^{2t−1} for 1 ≤ t ≤ d − s.
* The Z-free clause is a second conjunct, under deg_Z Q = 0. -/
theorem lemma_6_7 {F : Type*} [Field F] [IsAlgClosed F] (r d D B : ℕ) (hd : d < ringChar F)
    (Q : MvPolynomial (Fin (r + 3)) F) (hZ : Q.degreeOf 0 ≤ D) (hX : Q.degreeOf 1 ≤ D)
    (hY : Q.weightedTotalDegree (yWeight3 r) ≤ B) (hB : B < ringChar F) (hD : 2 ≤ D)
    (s : Fin (r + 1)) (hs : 0 < Q.degreeOf (yVar3 s))
    (hs' : ∀ j : Fin (r + 1), s < j → Q.degreeOf (yVar3 j) = 0) (α : F) :
    (∃ N : ℕ → MvPolynomial (Fin (d + 2)) F,
      (∀ t : ℕ, 1 ≤ t → (s : ℕ) + t ≤ d →
        (N t).totalDegree ≤ (2 * t - 1) * (D + B) ∧ ∀ v ∈ (N t).vars, (v : ℕ) ≤ (s : ℕ) + 1) ∧
      IsLiftedJet r d α s Q N) ∧
    (Q.degreeOf 0 = 0 → ∃ N : ℕ → MvPolynomial (Fin (d + 2)) F,
      (∀ t : ℕ, 1 ≤ t → (s : ℕ) + t ≤ d →
        (N t).totalDegree ≤ (2 * t - 1) * B ∧ ∀ v ∈ (N t).vars, (v : ℕ) ≤ (s : ℕ) + 1) ∧
      IsLiftedJet r d α s Q N) := by sorry

end RSCapacity
