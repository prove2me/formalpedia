-- Prove2me | Theorems.Thm_WeldedPath_lemma_3_11
-- name    : WeldedPath.lemma_3_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:19:40.52021+00:00
-- url     : https://prove2.me/theorems/59b92bc1-e154-42c3-b34e-3a6e0d885a20
-- title:
--   Lemma 3.11 — assignment tests before and after compression
-- statement:
--   Let $\mathrm P$ be a finite family of permutation registers, each of size at least $3$, with database registers, and let $\mathcal I_{\mathrm P}$ be the tensor product of the intertwiners (12) over the family. Let $\mathrm P_1,\dots,\mathrm P_m$ be registers of the family of sizes $s_j$ (not necessarily distinct), with database registers $\mathrm I_j$, and fix $x_j\in[s_j]$ and $Y_j\subseteq[s_j]$. Let
--   $$
--   \Pi_{x\to Y,\mathrm P}=\prod_{j=1}^m\sum_{y\in Y_j}\Pi_{\succeq\{(x_j,y)\},\mathrm P_j},\qquad \Pi_{x\to Y,\mathrm I}=\prod_{j=1}^m\sum_{y\in Y_j}\Pi_{\succeq\{(x_j,y)\},\mathrm I_j}
--   $$
--   test whether the permutations, resp. the databases, map $x_j$ into $Y_j$. There is an absolute constant $C$ such that: if $\xi$ is a possibly unnormalized state on the permutation registers and any additional registers with $(\Pi_{s_j,\le t})_{\mathrm P_j}\xi=\xi$ for all $j$, and $4(t+m+4)\le s\le\min_j s_j$, then
--   $$
--   \|\Pi_{x\to Y,\mathrm P}\,\xi\|\ \le\ \|\Pi_{x\to Y,\mathrm I}\,\mathcal I_{\mathrm P}\,\xi\|+C\sqrt{\frac1s\sum_{j=1}^m|Y_j|}\ \|\xi\| .
--   $$
--   The same holds for tests controlled by an additional register when the hypotheses and the error bound hold uniformly over the control values, and for inverse assignment tests $\prod_j\sum_{x\in X_j}\Pi_{\succeq\{(x,y_j)\}}$ with $|X_j|$ in place of $|Y_j|$.
--
--   The lemma converts "the permutation contains these assignments" into "the compressed database recorded them", at a cost that depends only on how many values are tested.
--
--   Differences from the source:
--   - generalization: I_P = I_M ⊗ ⨂_{b∈B_edge} I_{|E_b|} of (41), over the label and edge permutations → the product of the intertwiners (12) over any finite family of permutation registers of sizes ≥ 3; reason: the proof uses only that I_P is a tensor product of the isometries I_s (s ≥ 3, the standing assumption of §2, p.8, under which I_s is defined); the registers of (41) have sizes M + 1 and |E_b| ≥ N_l/4 ≥ 4, so (41) is an instance
--   - reading: projectors controlled by an additional register, hypotheses and error bound uniform over the control values → the number of tests, their registers, inputs and sets may depend on the control value c; the level hypothesis and 4(t + m_c + 4) ≤ s ≤ s_j hold for every c, and the error uses a common bound B ≥ Σ_j |Y_j| over c; reason: this is the uniformity the source asks for; a single control value is the uncontrolled lemma
--   - reading: there exists some constant C → one absolute constant C chosen before all other data; reason: the constant used in Theorem 3.12 does not depend on the instance
--   - encoding: registers P_j (not necessarily distinct), products of sums of projectors → a finite family of registers P_k, test j reading register reg j; diagonal projectors of the conjunction of the tests; reason: the tested projectors commute and are diagonal, so their product of sums is the indicator of the conjunction
--   - encoding: inverse assignment tests with y_j and X_j → flag inv = true: tests ϕ^{-1}(x_j) ∈ Y_j and I^{-1}(x_j) ∈ Y_j; reason: renaming y_j to x_j and X_j to Y_j
-- source:
--   Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder, Algorithmic Wave-Particle Duality: Pathfinding in Welded Trees is Hard, arXiv:2611.05912 (sha256 b31400a0…), Lemma 3.11, p.24

import Mathlib
import Definitions.Def_WeldedPath_piIntertwiner

namespace WeldedPath

open InjDb

/-- **Lemma 3.11** (Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder, arXiv:2611.05912
(sha256 b31400a0…), Lemma 3.11, p.24). For `j ∈ [m]` let `P_j` be a permutation register of size
`s_j` with database register `I_j` (the `P_j` need not be distinct), `x_j ∈ [s_j]`, `Y_j ⊆ [s_j]`,
`Π_{x→Y,P} = Π_j Σ_{y ∈ Y_j} Π_{⪰{(x_j,y)},P_j}` and `Π_{x→Y,I} = Π_j Σ_{y ∈ Y_j} Π_{⪰{(x_j,y)},I_j}`.
Let `ξ` be a possibly unnormalized state on `P` and any additional registers such that
`(Π_{s_j,≤t})_{P_j} ξ = ξ` for all `j ∈ [m]`, and assume `4(t + m + 4) ≤ s ≤ min_j s_j`. Then for
`I_P` as in (41), there exists some constant `C` such that
`‖Π_{x→Y,P} ξ‖ ≤ ‖Π_{x→Y,I} I_P ξ‖ + C √((1/s) Σ_{j=1}^m |Y_j|) ‖ξ‖`.
The same bound holds for the projectors controlled by an additional register assuming the
hypotheses and error bound hold uniformly over the control values. It also holds for inverse
assignment tests `Π_j Σ_{x ∈ X_j} Π_{⪰{(x,y_j)}}`, with `|X_j|` in place of `|Y_j|`.

**Formalization Note.**
1. The permutation registers are `P_k`, `k ∈ K`, of sizes `sz k`; test `j` reads register
   `reg c j`, so registers may repeat. The state `ξ` lives on a control register `Ctl`, additional
   registers `A` and the permutation registers; the tests (their number `m c`, registers, inputs
   and sets) depend on the control value `c`. One control value is the uncontrolled lemma.
2. The hypotheses hold uniformly over `c`: `(Π_{s_j,≤t})_{P_j}` fixes the `c`-component of `ξ`,
   `4(t + m_c + 4) ≤ s ≤ s_j`, and the error term uses a common bound `B ≥ Σ_j |Y_j|`.
3. `inv = false` gives the tests `ϕ_{P_j}(x_j) ∈ Y_j`, resp. `I_j(x_j) ∈ Y_j`; `inv = true` the
   inverse tests `ϕ_{P_j}^{-1}(x_j) ∈ Y_j`, resp. `I_j^{-1}(x_j) ∈ Y_j` (the source's `y_j`, `X_j`).
   Each product of sums of commuting diagonal projectors is the diagonal projector of the
   conjunction.
4. `C` is one absolute constant, chosen before every other datum.
5. `I_P` is the product of the intertwiners (12) over every register of the family, tested or
   not; (41) is the family of the label permutation and the edge classes. Every register has
   size `sz k ≥ 3`, the standing assumption of §2 (p.8) under which `I_s` is defined (the
   registers of (41) have sizes `M + 1` and `|E_b| ≥ N_l/4 ≥ 4`); the empty sum over levels
   makes `I_0 = 0`, which is not an isometry. -/
theorem lemma_3_11 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (K : Type) [Fintype K] [DecidableEq K] (sz : K → ℕ)
        (Ctl A : Type) [Fintype Ctl] [DecidableEq Ctl] [Fintype A] [DecidableEq A]
        (m : Ctl → ℕ) (reg : (c : Ctl) → Fin (m c) → K)
        (x : (c : Ctl) → (j : Fin (m c)) → Fin (sz (reg c j)))
        (Y : (c : Ctl) → (j : Fin (m c)) → Finset (Fin (sz (reg c j))))
        (inv : Bool) (s t : ℕ) (B : ℝ)
        (ξ : Hil (Ctl × (A × ((k : K) → Equiv.Perm (Fin (sz k)))))),
      (∀ k, 3 ≤ sz k) →
      (∀ c j, opTensor (ketBra (ket c) (ket c))
          (opTensor (1 : Hil A →L[ℂ] Hil A) (onFactor sz (reg c j) (projLe (sz (reg c j)) t))) ξ =
        opTensor (ketBra (ket c) (ket c))
          (1 : Hil (A × ((k : K) → Equiv.Perm (Fin (sz k)))) →L[ℂ] _) ξ) →
      (∀ c, 4 * (t + m c + 4) ≤ s) →
      (∀ c j, s ≤ sz (reg c j)) →
      (∀ c, (∑ j, ((Y c j).card : ℝ)) ≤ B) →
      ‖(diagProj fun p : Ctl × (A × ((k : K) → Equiv.Perm (Fin (sz k)))) =>
          ∀ j, (if inv then (p.2.2 (reg p.1 j)).symm (x p.1 j) else p.2.2 (reg p.1 j) (x p.1 j))
            ∈ Y p.1 j) ξ‖ ≤
        ‖(diagProj fun p : Ctl × (A × ((k : K) → InjDb (sz k))) =>
            ∀ j, ∃ y ∈ Y p.1 j,
              (if inv then (p.2.2 (reg p.1 j)).symm (x p.1 j) else p.2.2 (reg p.1 j) (x p.1 j)) =
                some y)
          (opTensor (1 : Hil Ctl →L[ℂ] Hil Ctl)
            (opTensor (1 : Hil A →L[ℂ] Hil A) (piIntertwiner sz)) ξ)‖ +
          C * Real.sqrt (B / s) * ‖ξ‖ := by sorry

end WeldedPath
