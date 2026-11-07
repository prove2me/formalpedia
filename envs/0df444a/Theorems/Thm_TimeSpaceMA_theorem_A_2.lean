-- Prove2me | Theorems.Thm_TimeSpaceMA_theorem_A_2
-- name    : TimeSpaceMA.theorem_A_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:58:14.133575+00:00
-- url     : https://prove2.me/theorems/d9de7f1b-d9c1-4f49-aa28-57d21bd19253
-- title:
--   Theorem A.2 — the hyperplane test [CMS20, Theorem 2]
-- statement:
--   Let $F$ be a field, $C\subseteq F^n$ a linear code of relative distance $\Delta$, and $k\ge3$. For every word $w\in F^{n^k}$,
--   $$\mathrm{dist}(w,C^{\otimes k})\le 12\Delta^{-k}\,\mathbb E_P\bigl[\mathrm{dist}(w|_P,C^{\otimes(k-1)})\bigr],$$
--   where $P$ is a uniformly random axis-parallel hyperplane, $w|_P$ is the restriction of $w$ to it, and $C^{\otimes k}$ is the set of words all of whose axis lines lie in $C$.
--
--   This result is cited from the literature; it drives the induction in the line-test bound.
--
--   Differences from the source:
--   - encoding: k ≥ 3 axes → k+1 axes with 3 ≤ k+1; reason: so that the hyperplane has k axes without a subtraction
--   - encoding: E_P → the average over axis i ∈ Fin (k+1) and value v ∈ Fin n; reason: the page's uniform choice of axis and value
--   - reading: relative distance ∆ → 0 < ∆ ≤ 1, n ≥ 1, and every nonzero codeword has at least ∆n nonzero coordinates; reason: ∆ > 1 only arises for the zero code, where the condition is vacuous and the bound would be false; on a nonzero code ∆ ≤ 1 is automatic and the true relative distance is the largest admissible ∆, so the page's statement is the instance at it
-- source:
--   Williams, Xi, Short Non-Interactive Proofs for Time-Space Computations, STOC 2027 submission (manuscript sha256 184c2f95…), Theorem A.2, p.32 (citing Chiesa, Manohar, Shinkar, Theory of Computing 16(5), 2020, Theorem 2)

import Definitions.Def_TimeSpaceMA_tensorEncode

namespace TimeSpaceMA

open Classical in
/-- **Theorem A.2** (Hyperplane Test [CMS20, Theorem 2]; Williams, Xi, STOC 2027 submission, manuscript
sha256 184c2f95…, p.32). For a linear code `C ⊆ F^n` of relative distance `∆`, `k ≥ 3`, and every word `w`:
`dist(w, C^{⊗k}) ≤ 12 ∆^{−k} E_P[dist(w|_P, C^{⊗(k−1)})]`, for `P` a uniformly random axis-parallel
hyperplane.

**Formalization Note** The theorem has `k + 1` axes with `k + 1 ≥ 3`, and `E_P` is the average over the axis
`i` and the value `v`. "Relative distance `∆`" is `0 < ∆ ≤ 1` and at least `∆ n` nonzero coordinates on each
nonzero codeword. The bound `∆ ≤ 1` is automatic unless `C = 0`, and excludes the junk reading of the zero
code, whose distance condition is vacuous. A smaller `∆` only weakens the bound's right side, so the lower
bound form specializes to the exact one. `n ≥ 1` keeps the fractions meaningful. -/
theorem theorem_A_2 {F : Type*} [Field F] {n : ℕ} (hn : 1 ≤ n) (C : Submodule F (Fin n → F)) (Δ : ℝ)
    (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1)
    (hC : ∀ y ∈ C, y ≠ 0 → Δ * (n : ℝ) ≤ ((Finset.univ.filter fun i => y i ≠ 0).card : ℝ))
    (k : ℕ) (hk : 3 ≤ k + 1) (w : (Fin (k + 1) → Fin n) → F) :
    distToSet w (tensorPowerCode C (k + 1)) ≤
      12 * (Δ⁻¹) ^ (k + 1) *
        ((1 / ((k + 1 : ℕ) : ℝ)) * (1 / (n : ℝ)) *
          ∑ i : Fin (k + 1), ∑ v : Fin n,
            distToSet (fun β : Fin k → Fin n => w (Fin.insertNth (α := fun _ => Fin n) i v β))
              (tensorPowerCode C k)) := by sorry

end TimeSpaceMA
