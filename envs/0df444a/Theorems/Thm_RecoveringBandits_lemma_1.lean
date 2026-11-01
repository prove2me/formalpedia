-- Prove2me | Theorems.Thm_RecoveringBandits_lemma_1
-- name    : RecoveringBandits.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:55:15.006985+00:00
-- url     : https://prove2.me/theorems/c429c419-35d6-47cc-95fd-4446eee2e064
-- title:
--   Lemma 1: $F_i$ is piecewise linear concave with nodes $1/d^{(k)}_i$ and dominates $F_{i,T}$
-- statement:
--   Let arm $i$ be admissible with supporting points $d^{(k)}_i$. Then:
--
--   1. $F_i$ is concave on $[0,1]$;
--   2. $F_i$ is affine on every interval $[1/d^{(k+1)}_i,\,1/d^{(k)}_i]$, $k\ge1$ (its changing points are in $\{1/d^{(k)}_i\}_{k\ge1}$);
--   3. $F_i(1/d^{(k)}_i)=R_i(d^{(k)}_i)/d^{(k)}_i$ for every $k\ge1$;
--   4. $F_i(x)=F_i(1/d^{(1)}_i)$ for all $x\in[1/d^{(1)}_i,1]$;
--   5. $F_i(x)\ge F_{i,T}(x)$ for all $T\ge1$ and $x\in[0,1]$.
--
--   The lemma makes the upper bound (3) a concave program whose solutions can be taken at the nodes $1/d^{(k)}_i$, which is what makes purely periodic policies natural.
--
--   Differences from the source:
--   - reading: F_i is piece-wise linear on [0,1] with changing points in {1/d^(k)_i} → F_i is affine on each [1/d^(k+1)_i, 1/d^(k)_i] (k ≥ 1) and constant on [1/d^(1)_i, 1]; reason: the supporting points increase strictly without bound, so these pieces cover (0,1]; this is what 'changing points in {1/d^(k)}' says
--   - encoding: for all i ∈ [N] → for one admissible arm r; reason: the statement is per arm; same instances
-- source:
--   Simchi-Levi–Zheng–Zhu, Offline Planning and Online Learning under Recovering Rewards, arXiv:2106.14813v2, Lemma 1, p.11

import Mathlib
import Definitions.Def_RecoveringBandits_Admissible
import Definitions.Def_RecoveringBandits_F
import Definitions.Def_RecoveringBandits_supp

namespace RecoveringBandits

/-- **Lemma 1**, Simchi-Levi–Zheng–Zhu, arXiv:2106.14813v2, Lemma 1, p.11 (PDF p.11): `F_i(x)` is
a piece-wise linear concave function on `[0, 1]` that satisfies:
* the changing points are in `{1/d^{(k)}_i}_{k ≥ 1}`;
* `F_i(1/d^{(k)}_i) = R_i(d^{(k)}_i)/d^{(k)}_i` for any `k ≥ 1`, and `F_i(x) = F_i(1/d^{(1)}_i)` for
  all `x ∈ [1/d^{(1)}_i, 1]`.
Meanwhile, `F_i(x) ≥ F_{i,T}(x)` for all `T ≥ 1`, `x ∈ [0, 1]`.

**Formalization Note.** "Piece-wise linear with changing points in `{1/d^{(k)}_i}`" is stated as:
`F_i` is affine on every `[1/d^{(k+1)}_i, 1/d^{(k)}_i]` (`k ≥ 1`) and constant on
`[1/d^{(1)}_i, 1]`. The supporting points increase strictly and without bound, so these pieces
cover `(0, 1]`. The statement is per arm (`r = R_i`). -/
theorem lemma_1 (r : ℕ → ℝ) (Rmax : ℝ) (hr : ArmAdmissible r Rmax) :
    ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (F r) ∧
    (∀ k : ℕ, 1 ≤ k → ∃ c m : ℝ, ∀ x ∈ Set.Icc (1 / (supp r (k + 1) : ℝ)) (1 / (supp r k : ℝ)),
      F r x = c + m * x) ∧
    (∀ k : ℕ, 1 ≤ k → F r (1 / (supp r k : ℝ)) = r (supp r k) / (supp r k : ℝ)) ∧
    (∀ x ∈ Set.Icc (1 / (supp r 1 : ℝ)) 1, F r x = F r (1 / (supp r 1 : ℝ))) ∧
    (∀ T : ℕ, 1 ≤ T → ∀ x ∈ Set.Icc (0 : ℝ) 1, FT r T x ≤ F r x) := by sorry

end RecoveringBandits
