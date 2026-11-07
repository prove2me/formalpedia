-- Prove2me | Theorems.Thm_SamplingLLL_lemma_A_4
-- name    : SamplingLLL.lemma_A_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:58:49.193211+00:00
-- url     : https://prove2.me/theorems/e790eb10-bffd-46d7-b28f-c8ec5f83ced5
-- title:
--   Lemma A.4, pp.20–21 — packet identity and deletion recursion
-- statement:
--   Let a task $(A,c)$, $c\notin A$, have a separated exploration, and let $Z(A)>0$. With $w_t=a_tZ(R_t)/Z(A)$ and $\nu_t=\lambda(\cdot\mid E_t,\text{every constraint in }R_t\text{ is satisfied})$,
--   $$
--   r_{A,c}=\sum_t\epsilon_ta_t\frac{Z(R_t)}{Z(A)}, \tag{2}
--   $$
--   $$
--   \mu_A\mathbf 1\{c\text{ is violated}\}+\sum_{\epsilon_t=-1}w_t\nu_t=\sum_{\epsilon_t=+1}w_t\nu_t. \tag{3}
--   $$
--   On every physical fibre the last-defect router couples the two sides of (3): every active leaf term has density $\lambda(x)/Z(A)$; if $c$ is satisfied there is no active leaf; if the bad set is exactly $\{c\}$ the unique active leaf is the all-no leaf, with positive sign; otherwise the router of Lemma A.3 pairs the positive and negative active leaves. If $D_t=(d_1,\dots,d_\ell)$, $A_0=R_t$, $A_j=A_{j-1}\cup\{d_j\}$, then
--   $$
--   w_t=a_t\prod_{j=1}^{\ell}\frac1{1-r_{A_{j-1},d_j}}, \tag{4}
--   $$
--   and every child task has target family strictly smaller than $A\cup\{c\}$.
--
--   Differences from the source:
--   - encoding: division by $Z(A)$ with its positivity left to the context → the hypothesis $0<Z(A)$; reason: it excludes only the case where $\mu_A$ is undefined
--   - encoding: "a measure-preserving coupling on every physical fibre" → the three fibre cases of the proof, p.21, with the density of each term; reason: this is the meaning given by the proof
--   - encoding: the separator data of the exploration → the fields of an `ExecData` at the task, which are arbitrary; reason: no instance changes
-- source:
--   Achlioptas, Counting and Sampling by Local Repair: From the Lovász Local Lemma to Random k-SAT, STOC 2027 submission (manuscript sha256 7a943167…), Lemma A.4, eqs. (2)–(4), pp.20–21

import Mathlib
import Definitions.Def_SamplingLLL_ExecAnalysis

set_option autoImplicit false

namespace SamplingLLL

open Classical in
/-- Lemma A.4 (Packet identity and deletion recursion), pp.20–21: (2), the measure identity (3), the
router coupling on every physical fibre, (4), and strictness of the children. Here
`w_t = a_t Z(R_t)/Z(A)` and `ν_t = λ(· | E_t, every constraint in R_t is satisfied)`; a zero-mass leaf
has `a_t = 0` by `at_`, so it is discarded.

Source: Achlioptas, STOC 2027 submission (manuscript sha256 7a943167…), Lemma A.4, pp.20–21.

**Formalization Note.** The exploration and its separators are the fields of `D` at the task `(A, c)`.
The hypothesis `0 < Z(A)` is the paper's standing use of division by `Z(A)`; it gives `Z(R_t) > 0` for
each `R_t ⊆ A`. The coupling is written fibre by fibre: no active leaf when `c` is satisfied, the all-no
leaf alone when the bad set is exactly `{c}`, the involution of Lemma A.3 otherwise. -/
theorem lemma_A_4 {n m : ℕ} {P : ProductCSP n m} (D : ExecData P) (A : Finset (Fin m)) (c : Fin m)
    (hc : c ∉ A) (hZ : 0 < P.Z A) (hnext : IsExploration (insert c A) c (D.next A c))
    (hsep : ∀ t ∈ D.leavesOf A c, Pos P A c t → D.Separated A c t) :
    let w : Leaf m → ℝ := fun t =>
      D.at_ A c t * ((P.Z (D.rest A c t) : ℚ) : ℝ) / ((P.Z A : ℚ) : ℝ)
    let ν : Leaf m → P.Config → ℝ := fun t x =>
      if P.active (insert c A) t x then ((P.mass x : ℚ) : ℝ) / ((P.leafMass (insert c A) t : ℚ) : ℝ)
      else 0
    ((P.viol A c : ℚ) : ℝ) = ∑ t ∈ D.leavesOf A c, (sign t : ℝ) * w t ∧
    (∀ x : P.Config,
      (if P.bad c x then ((P.mu A x : ℚ) : ℝ) else 0) +
          ∑ t ∈ (D.leavesOf A c).filter (fun t => sign t = -1), w t * ν t x =
        ∑ t ∈ (D.leavesOf A c).filter (fun t => sign t = 1), w t * ν t x) ∧
    (∀ x : P.Config, 0 < P.mass x →
      (∀ t ∈ D.leavesOf A c, P.active (insert c A) t x = true →
        w t * ν t x = ((P.mass x : ℚ) : ℝ) / ((P.Z A : ℚ) : ℝ)) ∧
      (P.bad c x = false → ∀ t ∈ D.leavesOf A c, P.active (insert c A) t x = false) ∧
      (P.badSet (insert c A) x = {c} →
        ((P.mu A x : ℚ) : ℝ) = ((P.mass x : ℚ) : ℝ) / ((P.Z A : ℚ) : ℝ) ∧
        sign (leafOf (D.next A c) c {c}) = 1 ∧
        ∀ t ∈ D.leavesOf A c, P.active (insert c A) t x = true ↔ t = leafOf (D.next A c) c {c}) ∧
      (P.bad c x = true → P.badSet (insert c A) x ≠ {c} →
        ∀ t ∈ D.leavesOf A c, P.active (insert c A) t x = true →
          let t' := routerLeaf (D.next A c) c (P.badSet (insert c A) x) t
          t' ∈ D.leavesOf A c ∧ P.active (insert c A) t' x = true ∧
          routerLeaf (D.next A c) c (P.badSet (insert c A) x) t' = t ∧
          sign t' = - sign t)) ∧
    (∀ t ∈ D.leavesOf A c, Pos P A c t →
      w t = D.at_ A c t *
        ((D.children A c t).map fun j => (1 - ((P.viol j.1 j.2 : ℚ) : ℝ))⁻¹).prod ∧
      ∀ j ∈ D.children A c t, insert j.2 j.1 ⊂ insert c A) := by sorry

end SamplingLLL
